# Lean 4 Search Agent

An intelligent search agent that finds relevant Lean 4 functions, structures, and theorems from the Batteries library using natural language queries.

## Features

- **Natural Language Search**: Describe what you need in plain English
- **LLM-Powered Analysis**: Extracts keywords and concepts using GPT-4o-mini
- **Rich Descriptions**: Every definition has a clear natural language explanation
- **Import Resolution**: Automatically provides the import statements you need
- **Fast Caching**: Instant results for repeated queries
- **Usage Hints**: Shows you how to use each function
- **Analytics**: Track search patterns and performance

## Quick Start

### Prerequisites

- Python 3.8+
- OpenAI API key
- Lean 4 project with Batteries library

### Installation

1. **Set up OpenAI API key:**

   Create `openai_key.txt` in the project root:
   ```bash
   echo "your-api-key-here" > ../../openai_key.txt
   ```

   Or set environment variable:
   ```bash
   export OPENAI_API_KEY="your-api-key-here"
   ```

2. **Install Python dependencies:**
   ```bash
   pip install openai
   ```

### Basic Usage

**Search for functions:**
```bash
python3 src/search_agent.py --task "multiply two natural numbers"
```

**Get more results:**
```bash
python3 src/search_agent.py --task "hash map operations" --max-results 10
```

**View statistics:**
```bash
python3 src/search_agent.py --stats
```

## Example Searches

### Example 1: Arithmetic Operations

```bash
python3 src/search_agent.py --task "multiply two natural numbers" --max-results 5
```

**Output:**
```
======================================================================
Search Results
======================================================================
Task: multiply two natural numbers
Found: 5 results
Time: 2.9s
Source: Fresh search

----------------------------------------------------------------------
1. Nat.mul (relevance: 3.85)

   Type: def
   Signature: Nat.mul : (@& Nat) → (@& Nat) → Nat

   Description: Multiplication of natural numbers, usually accessed via the
                `*` operator. This function is overridden in both the kernel
                and the compiler to efficiently evaluate using the arbitrary-
                precision arithmetic library.

   Import: import Batteries
   Usage: Nat.mul arg1 arg2 ...
----------------------------------------------------------------------
```

### Example 2: Data Structures

```bash
python3 src/search_agent.py --task "hash map with fast lookup"
```

**Output:**
```
1. _root_.Batteries.HashMap (relevance: 3.13)

   Type: structure
   Signature: _root_.Batteries.HashMap

   Description: `HashMap α β` is a key-value map which stores elements
                in an array using a hash function. Average O(1) lookup.

   Import: import Batteries
   Usage: Batteries.HashMap.mk ...
```

### Example 3: Array Operations

```bash
python3 src/search_agent.py --task "iterate over array and transform elements"
```

Finds `Array.map`, `Array.forM`, and related functions.

## CLI Reference

### Search Commands

```bash
# Basic search
python3 src/search_agent.py --task "your task description"

# Control number of results
python3 src/search_agent.py --task "find maximum" --max-results 20

# Bypass cache (force fresh search)
python3 src/search_agent.py --task "sort array" --no-cache

# Export results to JSON
python3 src/search_agent.py --task "hash operations" --output results.json

# Use different OpenAI model
python3 src/search_agent.py --task "prime numbers" --model gpt-4
```

### Maintenance Commands

```bash
# View search statistics
python3 src/search_agent.py --stats

# Rebuild the Lean function index
python3 src/search_agent.py --rebuild-index

# Enrich index with AI-generated descriptions (one-time)
python3 src/search_agent.py --enrich-index
```

## How It Works

### Architecture

```
User Query: "multiply two natural numbers"
    ↓
1. Cache Check (< 1ms if hit)
    ↓ (miss)
2. Task Analyzer (LLM extracts keywords: "mul", "multiply", "natural", "nat", ...)
    ↓
3. Searcher (ranks definitions using semantic scoring)
    - AI descriptions weighted 3x higher than docstrings
    - Name matches (e.g., "Nat.mul") also get bonus points
    ↓
4. Import Resolver (determines required imports)
    ↓
5. Format & Display Results
    ↓
6. Record in Database (for future cache hits)
```

### Components

1. **Task Analyzer** (`task_analyzer.py`)
   - Uses OpenAI GPT-4o-mini to extract keywords
   - Extracts both full terms ("multiply") and abbreviated forms ("mul")
   - Identifies types, operations, paradigms
   - Caches LLM responses to reduce costs

2. **Searcher** (`searcher.py`)
   - Multi-factor ranking algorithm with semantic weighting
   - **Scoring weights (optimized for natural language search):**
     - Exact name match: 10.0
     - Name contains keyword: 5.0
     - Name part matches: 4.0
     - **AI description match: 3.0** ← High weight for semantic understanding
     - Signature match: 2.0
     - Docstring match: 1.0
   - Uses pre-enriched index with AI-generated descriptions

3. **Import Resolver** (`import_resolver.py`)
   - Maps definitions to import statements
   - Handles Batteries library structure
   - Provides usage hints

4. **Database** (`database.py`)
   - SQLite storage for search history
   - LLM response caching
   - Analytics and statistics

5. **Index Enricher** (`enrich_index_descriptions.py`)
   - One-time batch process
   - Generates descriptions for all 482 definitions
   - 100% coverage of Batteries library

## Index Information

**Current Index:**
- **Batteries library** (482 definitions)
  - 272 functions (def)
  - 135 theorems
  - 28 structures
  - 21 type classes
  - 19 inductive types
- **Core library namespaces** (filtered)
  - Common types: `Nat`, `Int`, `Float`, `String`, `Char`
  - Collections: `Array`, `List`, `Option`, `Except`
  - Monadic: `IO`, `Monad`, `Functor`, `Applicative`
  - And 40+ more essential namespaces

**Coverage:**
- ✅ Batteries: Data structures, algorithms, utilities
- ✅ Core: Basic types and their operations (e.g., `Nat.mul`, `Float.atan2`)
- ✅ Monads and control flow
- ✅ IO and system operations

**Namespace Filtering:**
The Core library is indexed with namespace filtering to include only commonly-used types like `Nat`, `Float`, `String`, etc. This keeps the index focused and fast while providing access to essential standard library functions.

**NOT indexed:**
- Full Core library (too low-level - only selected namespaces)
- Local project files (focus on library functions)
- Mathlib (future enhancement)

## Performance

**Fresh Search (with LLM call):**
- Typical: 2-3 seconds
- Includes keyword extraction and ranking

**Cached Search:**
- Typical: < 1ms (instant)
- 50%+ cache hit rate after initial use

**LLM Caching:**
- Task analysis responses cached
- Saves money on repeated similar queries
- 7 cache hits in example session

## Advanced Usage

### Programmatic Use

```python
from search_agent import SearchAgent

# Initialize
agent = SearchAgent()

# Perform search
results = agent.search(
    task="multiply two natural numbers",
    max_results=10,
    use_cache=True
)

# Access results
for result in results['results']:
    print(f"{result['name']}: {result['description']}")
    print(f"Import: {result['import']}")
    print(f"Usage: {result['usage_hint']}")

# Get statistics
stats = agent.get_statistics()
print(f"Total searches: {stats['total_searches']}")

# Clean up
agent.close()
```

### Export to JSON

```bash
python3 src/search_agent.py --task "hash map" --output results.json
```

**Output format:**
```json
{
  "query_id": 1,
  "task": "hash map",
  "results": [
    {
      "name": "_root_.Batteries.HashMap",
      "type": "structure",
      "signature": "_root_.Batteries.HashMap",
      "description": "HashMap α β is a key-value map...",
      "import": "import Batteries",
      "opens": "open Std",
      "usage_hint": "Batteries.HashMap.mk ...",
      "score": 3.13
    }
  ],
  "execution_time_ms": 2.5,
  "from_cache": true
}
```

## Maintenance

### Rebuilding the Index

Run this when Batteries library is updated:

```bash
python3 src/search_agent.py --rebuild-index
```

This scans all Lean source files and extracts:
- Function definitions from Batteries
- Core library functions (filtered by namespace)
- Theorems, structures, classes
- Inductive types
- Doc comments

**Advanced indexing options:**

```bash
# Rebuild with custom Core namespaces
python3 src/lean_indexer.py --core-namespaces config/my_namespaces.txt

# Include all Core definitions (no filtering - may be slow)
python3 src/lean_indexer.py --no-core-filter

# Index only Batteries (no Core)
python3 src/lean_indexer.py --sources batteries

# Verbose output to see what's being indexed
python3 src/lean_indexer.py --verbose
```

### Re-enriching Descriptions

If you want to regenerate AI descriptions:

```bash
python3 src/search_agent.py --enrich-index
```

**Note:** This makes ~150 OpenAI API calls (~$0.05 total with gpt-4o-mini).

### Database Management

The database is stored at `data/search_history.db`. To reset:

```bash
rm data/search_history.db
```

Next search will recreate it automatically.

## File Structure

```
agents/search/
├── README.md                          # This file
├── src/
│   ├── search_agent.py               # Main CLI and orchestrator
│   ├── task_analyzer.py              # LLM keyword extraction
│   ├── searcher.py                   # Search and ranking
│   ├── import_resolver.py            # Import statement generation
│   ├── lean_indexer.py               # Index builder (with namespace filtering)
│   ├── enrich_index_descriptions.py  # Description generator
│   └── database.py                   # SQLite operations
├── config/
│   └── core_namespaces.txt           # Core library namespace whitelist
├── prompts/
│   ├── task_analyzer_system.txt      # Task analysis prompt
│   └── description_enricher_system.txt # Description generation prompt
├── data/
│   ├── lean_index.json               # Raw index (Batteries + Core namespaces)
│   ├── enriched_lean_index.json      # Index with descriptions
│   └── search_history.db             # SQLite database
├── tests/
│   ├── test_database.py
│   ├── test_lean_indexer.py
│   ├── test_task_analyzer.py
│   ├── test_searcher.py
│   └── test_import_resolver.py
└── docs/
    └── search_agent_plan.md          # Implementation plan
```

## Testing

Run individual test suites:

```bash
# Database tests
python3 tests/test_database.py

# Indexer tests
python3 tests/test_lean_indexer.py

# Task analyzer tests (add --with-llm for LLM tests)
python3 tests/test_task_analyzer.py
python3 tests/test_task_analyzer.py --with-llm

# Searcher tests
python3 tests/test_searcher.py

# Import resolver tests
python3 tests/test_import_resolver.py
```

All tests should pass with ✅.

## Troubleshooting

### "OpenAI API key not found"

**Solution:** Create `openai_key.txt` in project root or set `OPENAI_API_KEY` environment variable.

### "Index not found"

**Solution:** Rebuild the index:
```bash
python3 src/search_agent.py --rebuild-index
```

### "No results found"

**Possible causes:**
- Query too specific - try broader terms
- Batteries library doesn't have that functionality
- Try different keywords

**Example fixes:**
- Instead of: "fibonacci sequence generator"
- Try: "recursive function natural numbers"

### Slow searches

**Solution:** Cache is working! First search is slow (LLM call), subsequent identical searches are instant.

### High OpenAI costs

**Solutions:**
- Use `gpt-4o-mini` (default, very cheap)
- Cache is enabled by default
- Only task analysis uses LLM (not search itself)
- Typical cost: $0.001 per search (first time)

## Cost Analysis

**One-time costs:**
- Index enrichment: ~$0.05 (149 API calls)
- Done once, descriptions stored permanently

**Per-search costs:**
- Fresh search: ~$0.0001-0.0003 (task analysis only)
- Cached search: $0 (no API call)
- After 10 searches: ~50% cache hit rate
- After 100 searches: ~70% cache hit rate

**Monthly estimate (100 searches):**
- 50 fresh + 50 cached
- ~50 × $0.0002 = $0.01/month

Very affordable for development use!

## Design Philosophy

**Natural Language First:**
The search agent prioritizes semantic understanding over exact name matching. AI-generated descriptions receive 3x higher weight than docstrings because they're specifically written for natural language search. This means:

- ✅ Query "multiply two natural numbers" → finds `Nat.mul` (ranked #1)
- ✅ Query "hash map with fast lookup" → finds `HashMap` structure
- ✅ Query "iterate over array" → finds `Array.map`, `Array.forM`

**Hybrid Approach:**
Keywords include both:
- Full terms: "multiply", "multiplication", "product"
- Abbreviated forms: "mul" (as used in Lean names like `Nat.mul`)

This ensures results are relevant whether users describe operations naturally or use Lean terminology.

## Limitations

1. **Keyword-based matching**
   - Uses keyword extraction + weighted ranking
   - Not true semantic/embedding search
   - Future: Add vector embeddings for deeper semantic understanding

2. **English queries only**
   - LLM optimized for English
   - Could support other languages with prompt changes

3. **No code generation**
   - Finds functions, doesn't write code
   - Future: Integrate with code generation agent

4. **Single library focus**
   - Currently Batteries + selected Core namespaces
   - Mathlib integration planned

## Future Enhancements

### Planned Features

- [ ] Mathlib integration (100k+ definitions)
- [ ] Semantic search with embeddings
- [ ] Multi-library search (Batteries + Mathlib + local)
- [ ] Example code generation
- [ ] Interactive feedback ("was this helpful?")
- [ ] Web UI (currently CLI only)
- [ ] Incremental indexing (only re-index changed files)

### Integration Opportunities

This search agent is designed to be the first component in a larger multi-agent system:

```
Search Agent → Formalization Agent → Proof Agent → Repair Agent
```

See `../../docs/multi_agent_plan.md` for more details.

## Contributing

### Adding New Sources

To index additional libraries:

1. Update `lean_indexer.py` to include new source directories
2. Rebuild index: `python3 src/search_agent.py --rebuild-index`
3. Enrich with descriptions: `python3 src/search_agent.py --enrich-index`

### Customizing Core Namespaces

Edit `config/core_namespaces.txt` to control which Core library namespaces are indexed:

```txt
# Add any namespace prefix you want to include
Nat
Float
MyCustomNamespace
```

Lines starting with `#` are comments. Each namespace on its own line.

After modifying the config, rebuild the index:
```bash
python3 src/search_agent.py --rebuild-index
```

**Why namespace filtering?**
The Core library contains 10,000+ low-level definitions. Most users only need access to common types like `Nat`, `Float`, `String`, etc. Namespace filtering keeps the index focused, fast, and relevant while still providing access to essential standard library functions like `Nat.mul` and `Float.atan2`.

### Improving Prompts

Edit prompt templates in `prompts/` directory:
- `task_analyzer_system.txt` - Keyword extraction
- `description_enricher_system.txt` - Description generation

## Support

For issues, questions, or suggestions:
1. Check this README
2. Check `docs/search_agent_plan.md` for implementation details
3. Review test files for usage examples

## License

Part of the Tactics Generation project.

## Acknowledgments

- Built on Lean 4 and Batteries library
- Uses OpenAI GPT-4o-mini for natural language understanding
- Inspired by semantic code search tools

---

**Happy searching! 🔍**
