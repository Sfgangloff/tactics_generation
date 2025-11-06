#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
database.py

Database module for the search agent.
Handles search history, result caching, LLM response caching, and analytics.
"""

import sqlite3
import hashlib
import json
from datetime import datetime, timedelta
from typing import List, Optional, Dict, Any
from pathlib import Path


class SearchDatabase:
    """
    Manages the SQLite database for search agent operations.

    Responsibilities:
    - Store search queries and results
    - Cache LLM responses (task analysis, descriptions)
    - Track user feedback
    - Provide analytics
    """

    def __init__(self, db_path: str = "agents/search/data/search_history.db"):
        """Initialize database connection and create tables if needed."""
        self.db_path = db_path

        # Ensure parent directory exists
        Path(db_path).parent.mkdir(parents=True, exist_ok=True)

        self.conn = sqlite3.connect(db_path)
        self.conn.row_factory = sqlite3.Row  # Return rows as dicts
        self._init_tables()

    def _init_tables(self):
        """Create database tables if they don't exist."""
        cursor = self.conn.cursor()

        # Table 1: search_queries
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS search_queries (
                query_id INTEGER PRIMARY KEY AUTOINCREMENT,
                task_description TEXT NOT NULL,
                task_hash TEXT NOT NULL,
                keywords_extracted TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                execution_time_ms INTEGER,
                num_results INTEGER,
                sources_searched TEXT,
                lean_version TEXT
            )
        """)

        cursor.execute("""
            CREATE INDEX IF NOT EXISTS idx_task_hash
            ON search_queries(task_hash)
        """)

        cursor.execute("""
            CREATE INDEX IF NOT EXISTS idx_timestamp
            ON search_queries(timestamp)
        """)

        # Table 2: search_results
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS search_results (
                result_id INTEGER PRIMARY KEY AUTOINCREMENT,
                query_id INTEGER NOT NULL,
                definition_name TEXT NOT NULL,
                definition_type TEXT,
                signature TEXT,
                import_statement TEXT,
                description TEXT,
                docstring TEXT,
                file_path TEXT,
                relevance_score REAL,
                rank_position INTEGER,
                was_helpful INTEGER,
                FOREIGN KEY (query_id) REFERENCES search_queries(query_id)
            )
        """)

        cursor.execute("""
            CREATE INDEX IF NOT EXISTS idx_query_id
            ON search_results(query_id)
        """)

        cursor.execute("""
            CREATE INDEX IF NOT EXISTS idx_definition_name
            ON search_results(definition_name)
        """)

        # Table 3: llm_cache
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS llm_cache (
                cache_id INTEGER PRIMARY KEY AUTOINCREMENT,
                cache_type TEXT NOT NULL,
                input_hash TEXT NOT NULL,
                input_text TEXT,
                output_json TEXT,
                model_name TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                hit_count INTEGER DEFAULT 1
            )
        """)

        cursor.execute("""
            CREATE UNIQUE INDEX IF NOT EXISTS idx_cache_lookup
            ON llm_cache(cache_type, input_hash)
        """)

        # Table 4: similar_queries (for future analytics)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS similar_queries (
                query_id_1 INTEGER,
                query_id_2 INTEGER,
                similarity_score REAL,
                PRIMARY KEY (query_id_1, query_id_2),
                FOREIGN KEY (query_id_1) REFERENCES search_queries(query_id),
                FOREIGN KEY (query_id_2) REFERENCES search_queries(query_id)
            )
        """)

        self.conn.commit()

    def hash_query(self, task: str) -> str:
        """
        Create a hash of the query for exact match lookups.

        Args:
            task: The task description

        Returns:
            SHA256 hash of the normalized task
        """
        normalized = task.strip().lower()
        return hashlib.sha256(normalized.encode()).hexdigest()

    def check_cache(
        self,
        task: str,
        max_age_days: int = 30
    ) -> Optional[Dict[str, Any]]:
        """
        Check if this exact query was done before.

        Args:
            task: The task description
            max_age_days: Maximum age of cached results (default: 30 days)

        Returns:
            Cached results if found and recent enough, None otherwise
        """
        task_hash = self.hash_query(task)
        cursor = self.conn.cursor()

        # Find recent matching queries
        cutoff_date = datetime.now() - timedelta(days=max_age_days)
        cursor.execute("""
            SELECT query_id, timestamp, execution_time_ms, num_results
            FROM search_queries
            WHERE task_hash = ? AND timestamp > ?
            ORDER BY timestamp DESC
            LIMIT 1
        """, (task_hash, cutoff_date))

        query_row = cursor.fetchone()
        if not query_row:
            return None

        query_id = query_row['query_id']

        # Fetch results using helper (which maps column names)
        results = self._get_query_results(query_id)

        return {
            'query_id': query_id,
            'task': task,
            'timestamp': query_row['timestamp'],
            'relevant_items': results,
            'execution_time_ms': query_row['execution_time_ms'],
            'from_cache': True
        }

    def find_similar_queries(
        self,
        task: str,
        threshold: float = 0.8,
        max_results: int = 5
    ) -> List[Dict[str, Any]]:
        """
        Find similar queries using keyword overlap.

        Args:
            task: The task description
            threshold: Minimum similarity score (0-1)
            max_results: Maximum number of similar queries to return

        Returns:
            List of similar queries with their results
        """
        # Simple keyword overlap implementation
        # TODO: Enhance with embeddings-based similarity in future

        task_words = set(task.lower().split())
        cursor = self.conn.cursor()

        cursor.execute("""
            SELECT query_id, task_description, keywords_extracted
            FROM search_queries
            ORDER BY timestamp DESC
            LIMIT 100
        """)

        similar = []
        for row in cursor.fetchall():
            other_words = set(row['task_description'].lower().split())

            if len(task_words) == 0 or len(other_words) == 0:
                continue

            overlap = len(task_words & other_words)
            union = len(task_words | other_words)
            similarity = overlap / union if union > 0 else 0

            if similarity >= threshold:
                # Fetch results for this query
                results = self._get_query_results(row['query_id'])
                similar.append({
                    'query_id': row['query_id'],
                    'task': row['task_description'],
                    'similarity_score': similarity,
                    'results': results
                })

        # Sort by similarity and return top results
        similar.sort(key=lambda x: x['similarity_score'], reverse=True)
        return similar[:max_results]

    def _get_query_results(self, query_id: int) -> List[Dict[str, Any]]:
        """Helper: Get results for a specific query."""
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT definition_name, definition_type, signature, import_statement,
                   description, docstring, file_path, relevance_score, rank_position
            FROM search_results
            WHERE query_id = ?
            ORDER BY rank_position
        """, (query_id,))

        # Map database column names to expected format
        results = []
        for row in cursor.fetchall():
            results.append({
                'name': row['definition_name'],
                'type': row['definition_type'],
                'signature': row['signature'],
                'import': row['import_statement'],
                'description': row['description'],
                'docstring': row['docstring'],
                'file_path': row['file_path'],
                'relevance_score': row['relevance_score'],
                'rank_position': row['rank_position']
            })
        return results

    def record_search(
        self,
        task: str,
        keywords: List[str],
        results: List[Dict[str, Any]],
        execution_time_ms: int,
        sources: List[str],
        lean_version: str
    ) -> int:
        """
        Record a search query and its results in the database.

        Args:
            task: The task description
            keywords: Extracted keywords
            results: List of search results
            execution_time_ms: Time taken to execute search
            sources: List of sources searched (e.g., ['batteries', 'std'])
            lean_version: Lean 4 version string

        Returns:
            query_id for reference
        """
        task_hash = self.hash_query(task)
        cursor = self.conn.cursor()

        # Insert query
        cursor.execute("""
            INSERT INTO search_queries
            (task_description, task_hash, keywords_extracted,
             execution_time_ms, num_results, sources_searched, lean_version)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        """, (
            task, task_hash, json.dumps(keywords),
            execution_time_ms, len(results),
            ','.join(sources), lean_version
        ))

        query_id = cursor.lastrowid

        # Insert results
        for rank, result in enumerate(results, start=1):
            cursor.execute("""
                INSERT INTO search_results
                (query_id, definition_name, definition_type, signature,
                 import_statement, description, docstring, file_path,
                 relevance_score, rank_position)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                query_id,
                result.get('name'),
                result.get('type'),
                result.get('signature'),
                result.get('import'),
                result.get('description'),
                result.get('docstring'),
                result.get('file_path'),
                result.get('relevance_score'),
                rank
            ))

        self.conn.commit()
        return query_id

    def record_user_feedback(self, result_id: int, was_helpful: bool):
        """
        Record whether a result was helpful (for improving ranking).

        Args:
            result_id: The result ID from search_results table
            was_helpful: True if helpful, False if not
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            UPDATE search_results
            SET was_helpful = ?
            WHERE result_id = ?
        """, (1 if was_helpful else 0, result_id))
        self.conn.commit()

    def get_llm_cache(
        self,
        cache_type: str,
        input_text: str
    ) -> Optional[Dict[str, Any]]:
        """
        Check if we've already processed this LLM request.

        Args:
            cache_type: Type of cache ("task_analysis" or "description_generation")
            input_text: The input text to hash

        Returns:
            Cached output as dict, or None if not found
        """
        input_hash = hashlib.sha256(input_text.encode()).hexdigest()
        cursor = self.conn.cursor()

        cursor.execute("""
            SELECT output_json FROM llm_cache
            WHERE cache_type = ? AND input_hash = ?
        """, (cache_type, input_hash))

        result = cursor.fetchone()

        if result:
            # Increment hit count
            cursor.execute("""
                UPDATE llm_cache
                SET hit_count = hit_count + 1
                WHERE cache_type = ? AND input_hash = ?
            """, (cache_type, input_hash))
            self.conn.commit()

            return json.loads(result['output_json'])

        return None

    def save_llm_cache(
        self,
        cache_type: str,
        input_text: str,
        output: Dict[str, Any],
        model_name: str
    ):
        """
        Save LLM response for future reuse.

        Args:
            cache_type: Type of cache ("task_analysis" or "description_generation")
            input_text: The input text
            output: The LLM output as dict
            model_name: Name of the model used
        """
        input_hash = hashlib.sha256(input_text.encode()).hexdigest()
        cursor = self.conn.cursor()

        cursor.execute("""
            INSERT OR REPLACE INTO llm_cache
            (cache_type, input_hash, input_text, output_json, model_name)
            VALUES (?, ?, ?, ?, ?)
        """, (cache_type, input_hash, input_text, json.dumps(output), model_name))

        self.conn.commit()

    def get_search_stats(self) -> Dict[str, Any]:
        """
        Get overall statistics about searches.

        Returns:
            Dictionary with various statistics
        """
        cursor = self.conn.cursor()

        # Total searches
        cursor.execute("SELECT COUNT(*) as count FROM search_queries")
        total_searches = cursor.fetchone()['count']

        # Average execution time
        cursor.execute("SELECT AVG(execution_time_ms) as avg_time FROM search_queries")
        avg_time = cursor.fetchone()['avg_time'] or 0

        # Cache hit rate (queries under 100ms are likely cached)
        cursor.execute("""
            SELECT COUNT(*) as cached FROM search_queries
            WHERE execution_time_ms < 100
        """)
        cached_count = cursor.fetchone()['cached']
        cache_hit_rate = (cached_count / total_searches * 100) if total_searches > 0 else 0

        # Total LLM cache entries
        cursor.execute("SELECT COUNT(*) as count FROM llm_cache")
        llm_cache_count = cursor.fetchone()['count']

        # Total cache hits
        cursor.execute("SELECT SUM(hit_count) as total_hits FROM llm_cache")
        llm_cache_hits = cursor.fetchone()['total_hits'] or 0

        return {
            'total_searches': total_searches,
            'avg_execution_time_ms': round(avg_time, 2),
            'cache_hit_rate_percent': round(cache_hit_rate, 2),
            'llm_cache_entries': llm_cache_count,
            'llm_cache_hits': llm_cache_hits
        }

    def get_most_searched_terms(self, limit: int = 20) -> List[tuple]:
        """
        Get most common search keywords.

        Args:
            limit: Number of top terms to return

        Returns:
            List of (keyword, count) tuples
        """
        cursor = self.conn.cursor()

        cursor.execute("""
            SELECT keywords_extracted FROM search_queries
            WHERE keywords_extracted IS NOT NULL
        """)

        # Aggregate keywords
        keyword_counts = {}
        for row in cursor.fetchall():
            try:
                keywords = json.loads(row['keywords_extracted'])
                for keyword in keywords:
                    keyword_counts[keyword] = keyword_counts.get(keyword, 0) + 1
            except (json.JSONDecodeError, TypeError):
                continue

        # Sort and return top results
        sorted_keywords = sorted(keyword_counts.items(), key=lambda x: x[1], reverse=True)
        return sorted_keywords[:limit]

    def get_most_useful_definitions(self, limit: int = 20) -> List[tuple]:
        """
        Get definitions that appear most often in helpful results.

        Args:
            limit: Number of top definitions to return

        Returns:
            List of (definition_name, helpful_count, total_appearances) tuples
        """
        cursor = self.conn.cursor()

        cursor.execute("""
            SELECT definition_name,
                   COUNT(*) as appearances,
                   SUM(CASE WHEN was_helpful = 1 THEN 1 ELSE 0 END) as helpful_count
            FROM search_results
            WHERE was_helpful IS NOT NULL
            GROUP BY definition_name
            ORDER BY helpful_count DESC, appearances DESC
            LIMIT ?
        """, (limit,))

        return [(row['definition_name'], row['helpful_count'], row['appearances'])
                for row in cursor.fetchall()]

    def clear_old_cache(self, days: int = 30):
        """
        Clear cache entries older than specified days.

        Args:
            days: Age threshold in days
        """
        cutoff_date = datetime.now() - timedelta(days=days)
        cursor = self.conn.cursor()

        cursor.execute("""
            DELETE FROM search_queries
            WHERE timestamp < ?
        """, (cutoff_date,))

        cursor.execute("""
            DELETE FROM llm_cache
            WHERE timestamp < ?
        """, (cutoff_date,))

        self.conn.commit()

    def close(self):
        """Close the database connection."""
        self.conn.close()

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.close()
