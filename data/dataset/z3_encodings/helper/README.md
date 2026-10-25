# MathArena AIME Z3 Encodings

This tree contains hand-written Python/Z3 encodings for SMT-friendly
formalizations in `matharena.json`.

- `encodings/` contains problem encodings.
- `helper/` contains shared utilities, runners, and this README.

Each encoding prints only its computed result or final solver status. The
programs do not compare against dataset answers.

Run all current AIME encodings with:

```bash
source /project/aip-ksmeel/sunjia72/ecp_lpar/ecp/bin/activate
python /project/aip-ksmeel/sunjia72/ecp_lpar/data/dataset/z3_encodings/helper/run_aime_z3.py
```

Covered in this batch:

- AIME I: 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13
- AIME II: 1, 4, 5, 6, 8, 14, 15

Run the current HMMT/APEX encodings with:

```bash
source /project/aip-ksmeel/sunjia72/ecp_lpar/ecp/bin/activate
python /project/aip-ksmeel/sunjia72/ecp_lpar/data/dataset/z3_encodings/helper/run_hmmt_apex_z3.py
```

Covered in the HMMT/APEX batch:

- HMMT: 1, 2, 3, 8, 10, 11, 12, 13, 14, 15, 18, 21, 23
- APEX: 8, 10

Run exploratory wrong/partial candidate encodings with:

```bash
source /project/aip-ksmeel/sunjia72/ecp_lpar/ecp/bin/activate
python /project/aip-ksmeel/sunjia72/ecp_lpar/data/dataset/z3_encodings/helper/run_wrong_candidates_z3.py
```

These scripts finish within the current 30-second Z3 timeout but are not
counted as solved answer encodings because they are partial, normalized, or
relaxed formulations of:

- HMMT: 17, 24, 25, 30
- APEX: 2, 7

Run exploratory timeout-prone candidate encodings with:

```bash
source /project/aip-ksmeel/sunjia72/ecp_lpar/ecp/bin/activate
python /project/aip-ksmeel/sunjia72/ecp_lpar/data/dataset/z3_encodings/helper/run_timeout_candidates_z3.py
```

These scripts are not counted as solved answer encodings because Z3 returns
`unknown` due to the 30-second timeout:

- HMMT: 7, 20, 22
- APEX: 12

The remaining problems are less direct SMT targets in their current Lean form
because they involve heavier geometry, transcendental/infinite sums, paths over
large variable-length objects, continuity/limits/integrals, or complex
polynomial reasoning. They may still be encodable after problem-specific
reductions.
