# Search Agent: Implementation Plan

**Version:** 1.0  
**Date:** 2025-11-06  
**Status:** Planning Phase

---

## 🎯 Overview

### Goal

Build an intelligent search agent that takes natural language task descriptions and finds relevant Lean 4 functions, structures, and type classes from Batteries, Std, Core, and (eventually) Mathlib libraries.

### Example

**Input:**
```
"create a function which gives the area of a square in lean using imperative programming"
```

**Output:**
```json
{
  "query_id": 42,
  "task": "create a function which gives the area of a square in lean using imperative programming",
  "relevant_items": [
    {
      "name": "Nat.mul",
      "type": "function",
      "signature": "Nat.mul : Nat → Nat → Nat",
      "import": "Prelude",
      "description": "Multiplies two natural numbers",
      "relevance_score": 0.95,
      "file_path": "Init/Data/Nat/Basic.lean"
    },
    {
      "name": "Id.run",
      "type": "function",
      "signature": "Id.run : {α : Type u} → Id α → α",
      "import": "Init.Core",
      "description": "Runs an imperative computation in the Id monad",
      "relevance_score": 0.88
    }
  ],
  "execution_time_ms": 245,
  "from_cache": false
}
```

---

## 🏗️ Architecture

### High-Level Flow

```
                    ONE-TIME ENRICHMENT (Phase 1.5):
┌─────────────────┐
│ Lean Source     │
│ Files (.lean)   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Lean Indexer   │
│ (Extract defs)  │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ lean_index.json │ (raw: names, sigs, docstrings)
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Description     │◄──────── LLM (batch process)
│ Enricher        │◄──────── Source code context
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ enriched_index  │ (includes NL descriptions)
│ .json           │
└─────────────────┘

                    SEARCH TIME (fast, no LLM):
┌─────────────────┐
│  User Query     │
│  (Natural Lang) │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Cache Check    │◄──────── Search History DB
└────────┬────────┘
         │ (miss)
         ▼
┌─────────────────┐
│ Task Analyzer   │◄──────── LLM Cache
│ (Extract        │
│  Keywords)      │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Searcher       │◄──────── Enriched Index
│ (Keyword →      │           (with descriptions)
│  Definitions)   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Import Resolver │
│ (Add imports)   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│   Ranking &     │
│   Filtering     │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Record in DB   │──────► Search History DB
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Return Results │
└─────────────────┘
```

---

## 📦 Core Components

### 1. Database Module (`database.py`)

**Purpose:** Store search history, cache LLM responses, enable analytics

**Schema:**

**Table: `search_queries`**
- `query_id` (PK)
- `task_description` (TEXT)
- `task_hash` (TEXT, indexed)
- `keywords_extracted` (JSON)
- `timestamp` (DATETIME)
- `execution_time_ms` (INTEGER)
- `num_results` (INTEGER)
- `sources_searched` (TEXT)
- `lean_version` (TEXT)

**Table: `search_results`**
- `result_id` (PK)
- `query_id` (FK)
- `definition_name` (TEXT)
- `definition_type` (TEXT)
- `signature` (TEXT)
- `import_statement` (TEXT)
- `description` (TEXT)
- `docstring` (TEXT)
- `file_path` (TEXT)
- `relevance_score` (REAL)
- `rank_position` (INTEGER)
- `was_helpful` (INTEGER, NULL/0/1)

**Table: `llm_cache`**
- `cache_id` (PK)
- `cache_type` (TEXT: "task_analysis" or "description_generation")
- `input_hash` (TEXT, indexed)
- `input_text` (TEXT)
- `output_json` (TEXT)
- `model_name` (TEXT)
- `timestamp` (DATETIME)
- `hit_count` (INTEGER)

**Table: `similar_queries`**
- `query_id_1` (FK)
- `query_id_2` (FK)
- `similarity_score` (REAL)

**Key Operations:**
- `check_cache(task)` → Returns cached results if exact match found
- `find_similar_queries(task, threshold)` → Returns similar past queries
- `record_search(task, keywords, results, ...)` → Saves search to DB
- `get_llm_cache(cache_type, input)` → Retrieves cached LLM response
- `save_llm_cache(cache_type, input, output)` → Caches LLM response
- `record_user_feedback(result_id, was_helpful)` → User feedback
- `get_search_stats()` → Analytics

---

### 2. Lean Indexer (`lean_indexer.py`)

**Purpose:** Build searchable index of Lean definitions

**Strategy:** File-based parsing (MVP), LSP-based (future)

**Index Format (JSON):**
```json
{
  "Nat.mul": {
    "type": "function",
    "signature": "Nat.mul : Nat → Nat → Nat",
    "file_path": "Init/Data/Nat/Basic.lean",
    "docstring": "Multiplication of natural numbers",
    "line_number": 123,
    "module": "Init.Data.Nat.Basic"
  },
  ...
}
```

**Key Operations:**
- `build_index(source_dirs)` → Scans .lean files, extracts definitions
- `rebuild_index()` → Rebuilds index from scratch
- `get_lean_version()` → Returns current Lean version

**Sources to Index:**
1. **Batteries** (.lake/packages/batteries/Batteries/)
   - Includes standard library functionality (Std is integrated in Batteries v4)
   - Data structures: HashMap, HashSet, BinaryHeap, Array extensions
   - Control structures: monads, functors, applicatives
   - Tactics and automation helpers

**Not Indexed (excluded from current scope):**
- ~~Core library~~ - Too low-level, Batteries provides better interfaces
- ~~Local project files~~ - Searching own code not the primary goal
- ~~Mathlib~~ - Future enhancement, very large (~100k+ definitions)

**Extraction Method:**
- Regex patterns for: `def`, `theorem`, `structure`, `class`, `inductive`
- Extract doc comments: `/-! ... -/` and `/-- ... -/`
- Extract type signatures

---

### 3. Task Analyzer (`task_analyzer.py`)

**Purpose:** Extract keywords and concepts from natural language task

**LLM Prompt Template:** `prompts/task_analyzer_system.txt`

**Key Features:**
- Extracts both full terms ("multiply") and abbreviated forms ("mul")
- Identifies Lean-specific terminology (e.g., "Nat" for natural numbers)
- Captures 3-10 keywords per query for semantic richness

**Example Input:**
```
"multiply two natural numbers"
```

**Example Output:**
```json
{
  "keywords": ["mul", "multiply", "product", "times", "multiplication", "natural", "number", "arithmetic"],
  "types": ["Nat", "Int"],
  "operations": ["multiply", "multiplication"],
  "paradigm": null,
  "domain": "arithmetic"
}
```

**Key Operations:**
- `analyze_task(task_description)` → Extracts structured information
- Uses OpenAI API (gpt-4o-mini by default) with structured JSON output
- Results are cached in `llm_cache` table
- Hybrid approach: Natural language terms + Lean abbreviated forms

---

### 4. Searcher (`searcher.py`)

**Purpose:** Find relevant definitions based on keywords

**Search Strategies:**
1. **Exact name match** (highest priority)
2. **Name contains keyword** (partial match)
3. **Docstring contains keyword** (semantic relevance)
4. **Type signature contains keyword** (type-based)

**Ranking Factors (Optimized for Natural Language):**
- **AI description matches (3.0)** - Highest semantic weight
- **Exact name matches (10.0)** - Function name exactly matches keyword
- **Partial name matches (5.0)** - Keyword appears in name
- **Name part matches (4.0)** - Keyword matches name component (e.g., "map" in "HashMap")
- **Signature matches (2.0)** - Keyword in type signature
- **Docstring matches (1.0)** - Keyword in original docstring
- Type preference bonus (1.2x for preferred types)
- Docstring existence bonus (1.1x for documented functions)

**Design Philosophy:**
AI descriptions get 3x weight vs docstrings because they're specifically generated
for natural language search. This enables queries like "multiply two natural numbers"
to correctly find `Nat.mul` (ranked #1) even though "multiply" doesn't appear in the
function name.

**Key Operations:**
- `search_definitions(keywords, index, max_results)` → Returns ranked results
- `_score_definition(name, defn, keywords, prefer_types)` → Calculates relevance score

---

### 5. Import Resolver (`import_resolver.py`)

**Purpose:** Convert file paths to Lean import statements

**Examples:**
- `~/.elan/.../library/Init/Data/Nat/Basic.lean` → `import Init.Data.Nat.Basic`
- `lake-packages/batteries/Batteries/Data/Array.lean` → `import Batteries.Data.Array`
- `TacticsGeneration/Benchmark.lean` → `import TacticsGeneration.Benchmark`

**Key Operations:**
- `resolve_imports(file_path, lean_root)` → Returns import statement
- Handles core library, lake packages, and local files

---

### 6. Description Enricher (`enrich_index_descriptions.py`)

**Purpose:** Pre-generate natural language descriptions for ALL definitions in the index

**Strategy:**
1. **One-time batch process** that enriches the index with descriptions
2. If docstring exists → use it as-is
3. If docstring missing → generate via LLM (with source code context)
4. Save enriched index with descriptions included

**LLM Prompt Template:** `prompts/description_enricher_system.txt`

**Process Flow:**
```
lean_index.json (raw)
    ↓
Read index + Load source code for each definition
    ↓
For each definition without good docstring:
    - Extract surrounding code context
    - Call LLM to generate description
    - Cache result
    ↓
Save enriched_lean_index.json (with descriptions)
```

**Key Operations:**
- `enrich_index(index_path, output_path)` → Adds descriptions to entire index
- `generate_description(name, signature, source_code)` → Returns description
- `load_source_context(file_path, line_number)` → Extracts code context
- Results are permanently stored in enriched index (no runtime LLM calls)

**Benefits:**
- **Much faster searches** (no LLM calls at search time)
- **Lower costs** (generate descriptions once, use many times)
- **Better descriptions** (can use source code context, not just signatures)
- **Offline operation** (searches don't need API access)

---

### 7. Main Search Agent (`search_agent.py`)

**Purpose:** Orchestrate all components

**Flow:**
1. Check database for exact cache hit
2. Check for similar queries (reuse if similarity > 0.95)
3. Analyze task (with LLM caching)
4. Search index for definitions
5. Resolve imports for each result
6. Generate descriptions (with LLM caching)
7. Rank by relevance
8. Record in database
9. Return results

**CLI Interface:**
```bash
# Basic search
python3 scripts/search_agent.py \
  --task "multiply two natural numbers" \
  --sources batteries std core \
  --max-results 10 \
  --output results.json

# Rebuild index
python3 scripts/search_agent.py --rebuild-index

# View statistics
python3 scripts/search_agent.py --stats

# Export history
python3 scripts/search_agent.py --export-history searches.csv

# Top searches
python3 scripts/search_agent.py --top-searches 20
```

---

## 📂 File Structure

```
tactics_generation/
├── scripts/
│   └── search_agent/
│       ├── __init__.py
│       ├── search_agent.py          # Main entry point & CLI
│       ├── database.py              # Database operations & caching
│       ├── task_analyzer.py         # Task → keywords (LLM)
│       ├── lean_indexer.py          # Build searchable index
│       ├── searcher.py              # Keyword → definitions
│       ├── import_resolver.py       # File path → import statement
│       └── description_generator.py # Signature → NL description (LLM)
├── prompts/
│   ├── search_task_analyzer.txt     # LLM prompt: task analysis
│   └── search_description_gen.txt   # LLM prompt: description generation
├── data/
│   ├── lean_index.json              # Pre-built index of Lean definitions
│   └── search_history.db            # SQLite: searches, results, cache
├── docs/
│   └── search_agent_plan.md         # This document
└── tests/
    ├── test_search_agent.py         # Integration tests
    ├── test_database.py             # Database tests
    ├── test_indexer.py              # Indexer tests
    └── test_searcher.py             # Searcher tests
```

---

## 🚀 Implementation Phases

### Phase 0: Setup (Day 1, Morning)

**Tasks:**
- [ ] Create directory structure: `scripts/search_agent/`
- [ ] Create `__init__.py` files
- [ ] Set up SQLite database schema (`database.py`)
- [ ] Write database initialization script
- [ ] Create prompt templates directory structure

**Deliverables:**
- Empty module structure
- Database with tables created
- Basic `database.py` with CRUD operations

---

### Phase 1: Lean Indexer (Day 1, Afternoon)

**Tasks:**
- [ ] Implement `lean_indexer.py`
- [ ] Write regex patterns for Lean definitions
- [ ] Handle doc comment extraction
- [ ] Scan Core, Batteries, Std libraries
- [ ] Save index to `data/lean_index.json`
- [ ] Add `--rebuild-index` CLI flag

**Test Cases:**
- Index finds `Nat.mul`, `Array.forM`, `List.map`
- Extracts correct signatures
- Extracts doc comments when present
- Handles files without errors

**Deliverables:**
- Working indexer
- Initial index file (JSON)
- ~1000+ definitions indexed

---

### Phase 2: Task Analyzer (Day 2, Morning)

**Tasks:**
- [ ] Create prompt template: `prompts/search_task_analyzer.txt`
- [ ] Implement `task_analyzer.py`
- [ ] Integrate with OpenAI API
- [ ] Add LLM caching via `database.py`
- [ ] Test with example queries

**Test Cases:**
- "multiply two numbers" → keywords: ["multiply", "numbers", "arithmetic"]
- "iterate over array" → keywords: ["iterate", "loop", "array", "for"]
- "check prime imperative" → paradigm: "imperative"

**Deliverables:**
- Working task analyzer
- Prompt template
- LLM caching functional

---

### Phase 3: Searcher (Day 2, Afternoon)

**Tasks:**
- [ ] Implement `searcher.py`
- [ ] Implement exact name matching
- [ ] Implement partial name matching
- [ ] Implement docstring search
- [ ] Implement ranking algorithm
- [ ] Test with indexed data

**Test Cases:**
- Search "mul" finds `Nat.mul`, `Int.mul`, `Float.mul`
- Search "array iterate" finds `Array.forM`, `Array.map`
- Results ranked by relevance

**Deliverables:**
- Working searcher
- Ranked results
- Top 10 results for each test query

---

### Phase 4: Import Resolver (Day 3, Morning)

**Tasks:**
- [ ] Implement `import_resolver.py`
- [ ] Handle core library paths
- [ ] Handle lake-packages paths
- [ ] Handle local project paths
- [ ] Test edge cases

**Test Cases:**
- Core file → `import Init.Data.Nat.Basic`
- Batteries file → `import Batteries.Data.Array`
- Local file → `import TacticsGeneration.Benchmark`

**Deliverables:**
- Working import resolver
- Handles all source types

---

### Phase 5: Description Enricher (Day 3, Afternoon)

**Tasks:**
- [ ] Create prompt template: `prompts/description_enricher_system.txt`
- [ ] Implement `enrich_index_descriptions.py`
- [ ] Add function to load source code context around definitions
- [ ] Batch process entire index to generate descriptions
- [ ] Use existing docstrings when they're good quality
- [ ] Generate descriptions via LLM for missing/poor docstrings
- [ ] Save enriched index with descriptions included
- [ ] Add CLI flag: `--enrich-index` to run enrichment

**Test Cases:**
- Definition with good docstring → keeps docstring
- Definition without docstring → generates description from code
- Definition with signature → generates clear explanation
- Enriched index contains all original data plus descriptions

**Deliverables:**
- Working description enricher
- Prompt template optimized for batch processing
- Enriched index file: `enriched_lean_index.json`
- All 482 definitions have natural language descriptions

---

### Phase 6: Integration & CLI (Day 4)

**Tasks:**
- [ ] Implement main `search_agent.py`
- [ ] Integrate all components
- [ ] Add CLI argument parsing
- [ ] Add cache checking logic
- [ ] Add similar query detection
- [ ] Test end-to-end flow
- [ ] Add analytics commands (--stats, --export-history)

**Test Cases:**
- Full pipeline: task → results
- Cache hit returns instantly
- Similar query reuse works
- All CLI flags functional

**Deliverables:**
- Working search agent CLI
- End-to-end functionality
- Database recording all searches

---

### Phase 7: Testing & Refinement (Day 5)

**Tasks:**
- [ ] Create comprehensive test suite
- [ ] Test with diverse queries
- [ ] Measure performance (execution time)
- [ ] Evaluate result quality (precision/recall)
- [ ] Refine prompts based on results
- [ ] Optimize ranking algorithm
- [ ] Add error handling
- [ ] Write usage documentation

**Test Queries:**
1. "multiply two natural numbers"
2. "create an array and iterate over it"
3. "check if a number is prime using a for loop"
4. "find the maximum element in a list"
5. "read input from user in IO"
6. "sort an array of integers"
7. "calculate factorial recursively"
8. "convert string to integer"

**Deliverables:**
- Test suite (pytest)
- Performance benchmarks
- Quality metrics
- Usage documentation

---

## ✅ Success Criteria

The search agent is successful when:

1. ✅ **Accuracy**: Top 3 results are relevant for 80%+ of test queries
2. ✅ **Speed**: Queries complete in < 5 seconds (uncached), < 0.1s (cached)
3. ✅ **Coverage**: Index contains 1000+ definitions from Core/Batteries/Std
4. ✅ **Caching**: Cache hit rate > 50% after 100 queries
5. ✅ **Imports**: All results have correct import statements
6. ✅ **Descriptions**: All results have clear natural language descriptions
7. ✅ **Reliability**: Handles edge cases without crashing

---

## 📊 Analytics & Monitoring

### Metrics to Track

**Performance Metrics:**
- Average execution time (cached vs uncached)
- Cache hit rate
- Index build time
- LLM API call count and cost

**Quality Metrics:**
- Result relevance (manual evaluation)
- User feedback scores (was_helpful)
- Keyword extraction accuracy

**Usage Metrics:**
- Total searches performed
- Most common search terms
- Most frequently returned definitions
- Peak usage times

### Analytics Queries

```sql
-- Most common keywords
SELECT keyword, COUNT(*) as count
FROM (SELECT json_each.value as keyword 
      FROM search_queries, json_each(keywords_extracted))
GROUP BY keyword
ORDER BY count DESC
LIMIT 20;

-- Most useful definitions
SELECT definition_name, COUNT(*) as appearances,
       SUM(was_helpful) as helpful_count
FROM search_results
WHERE was_helpful IS NOT NULL
GROUP BY definition_name
ORDER BY helpful_count DESC
LIMIT 20;

-- Cache hit rate
SELECT 
  (SELECT COUNT(*) FROM search_queries WHERE execution_time_ms < 100) * 100.0 /
  (SELECT COUNT(*) FROM search_queries) as cache_hit_rate_percent;
```

---

## 🔄 Future Enhancements

### Phase 8: Semantic Search (Future)

**Additions:**
- Embed task descriptions and definitions using sentence-transformers
- Use vector similarity instead of keyword matching
- Add FAISS or similar vector database

**Benefits:**
- Find semantically similar definitions
- Better handling of synonyms and paraphrases

---

### Phase 9: Advanced Features (Future)

**Additions:**
- **Example code generation**: Generate usage examples for each result
- **Dependency graphs**: Show related functions/types
- **Interactive feedback**: User marks results as helpful/not helpful
- **Incremental indexing**: Only re-index changed files
- **Web UI**: Browser-based interface instead of CLI
- **Mathlib integration**: Full Mathlib indexing (large scale)
- **Multi-agent integration**: Pass results to code generation agent

---

### Phase 10: Optimization (Future)

**Improvements:**
- Parallel indexing for faster index builds
- PostgreSQL instead of SQLite for better concurrency
- Redis cache layer for ultra-fast lookups
- Approximate nearest neighbor search for embeddings
- Query expansion (related terms)

---

## 🔗 Integration with Multi-Agent System

The search agent will be the first agent in the multi-agent system:

```
User Task
    ↓
Search Agent (finds relevant Lean definitions)
    ↓
Formalization Agent (uses results to formalize theorem)
    ↓
Proof Agent (generates proof using suggested functions)
    ↓
Repair Agent (fixes any errors)
    ↓
Final Formalized Theorem
```

**Future Integration Points:**
- Pass search results directly to code generation agent
- Use search history to improve formalization prompts
- Feed search analytics back to improve ranking
- Cross-reference with knowledge base of proven theorems

---

## 📝 Notes

### Key Design Decisions

**Why SQLite?**
- Simple, embedded, no separate server
- Good enough for MVP (thousands of queries)
- Can migrate to PostgreSQL later if needed

**Why keyword-based search first?**
- Simpler to implement and debug
- Fast (no embedding computation)
- Good baseline for comparison
- Can add semantic search later

**Why cache LLM responses?**
- Significant cost savings (each API call costs money)
- Faster response times
- Reduces API rate limit issues
- Enables offline operation for repeated queries

**Why index at build time?**
- Lean libraries change infrequently
- Faster query time (no on-the-fly parsing)
- Can rebuild when Lean version changes

---

## 🐛 Known Challenges & Mitigation

### Challenge 1: Lean Parsing Complexity

**Problem:** Lean 4 syntax is complex; regex may miss definitions

**Mitigation:**
- Start with simple patterns (def, theorem, structure)
- Improve incrementally based on test results
- Future: Use Lean's LSP server for robust parsing

### Challenge 2: Import Path Resolution

**Problem:** Determining correct imports can be tricky

**Mitigation:**
- Start with common cases (core, batteries, std)
- Test extensively with known definitions
- Document edge cases and handle explicitly

### Challenge 3: Result Relevance

**Problem:** Keyword matching may return irrelevant results

**Mitigation:**
- Use ranking algorithm to prioritize best matches
- Collect user feedback to improve over time
- Add semantic search in future phases

### Challenge 4: Index Freshness

**Problem:** Index becomes stale when Lean libraries update

**Mitigation:**
- Store Lean version with index
- Rebuild index when version changes
- Add `--rebuild-index` flag for manual updates
- Future: Incremental indexing

---

## 📚 References

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Batteries Documentation](https://github.com/leanprover-community/batteries)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [OpenAI API Documentation](https://platform.openai.com/docs/api-reference)

---

**Document Version:** 1.0  
**Last Updated:** 2025-11-06  
**Next Review:** After Phase 7 completion
