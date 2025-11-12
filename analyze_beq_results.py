import json
import sys

filename = sys.argv[1] if len(sys.argv) > 1 else 'reports/beq_test_results.json'
with open(filename, 'r', encoding='utf-8') as f:
    results = json.load(f)

print("=" * 70)
print("BEq+ Test Results")
print("=" * 70)

test_cases = [x for x in results['results'] if x['id'].startswith('beq_test')]

for i, test in enumerate(test_cases, 1):
    print(f"\nTest {i}: {test['id']}")
    print(f"  Status: {test['status']}")
    print(f"  Tier: {test.get('tier', 'N/A')}")
    print(f"  Reason: {test.get('reason', 'N/A')}")
    print(f"  BEq+ Attempted: {test.get('beq_plus_attempted', False)}")
    if test.get('beq_plus_attempted'):
        print(f"  BEq+ Left (P→Q): {test.get('beq_plus_left', 'N/A')}")
        print(f"  BEq+ Right (Q→P): {test.get('beq_plus_right', 'N/A')}")
        print(f"  BEq+ Strategy: {test.get('beq_plus_strategy', 'N/A')}")
        logs = test.get('beq_plus_logs', {})
        stderr = logs.get('stdout_stderr', '')
        if stderr:
            # Show first 300 chars of error
            error_preview = stderr[:300].replace('\n', ' ')
            print(f"  Error Preview: {error_preview}")
        elapsed = logs.get('elapsed_s', 'N/A')
        print(f"  Elapsed Time: {elapsed}s")

print("\n" + "=" * 70)

