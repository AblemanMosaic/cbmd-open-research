"""A process-custody smoke example. No research claim is attached."""
import json

print(json.dumps({"example": "integer_arithmetic_probe", "value": sum(range(11)),
                  "claim_boundary": "PROCESS_SMOKE_ONLY"}, sort_keys=True))
