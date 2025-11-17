# Documentation Guide - What to Trust

**Purpose**: Clarify which documentation files are authoritative vs internal notes
**Date**: 2025-01-17

---

## ✅ Authoritative Public-Facing Documentation

These files are **authoritative** and **fully consistent** with current statistics:

### 1. **README.md** ⭐ PRIMARY SOURCE
- **Status**: ✅ Up to date
- **Statistics**: 90 statements (45 theorems + 45 axioms), 34 complete, 11 incomplete
- **Purpose**: Main repository documentation for all users
- **Trust Level**: **100% - Use this as the definitive source**

### 2. **THEOREM_INVENTORY.md** ⭐ PRIMARY SOURCE
- **Status**: ✅ Up to date
- **Statistics**: Detailed breakdown by appendix with accurate counts
- **Purpose**: Complete theorem index and coverage summary
- **Trust Level**: **100% - Authoritative theorem reference**

### 3. **CITATION.cff**
- **Status**: ✅ Up to date
- **Statistics**: Accurate abstract with 90 statements, 34 complete proofs
- **Purpose**: GitHub citation metadata
- **Trust Level**: **100% - Authoritative for citations**

### 4. **THEOREM_INDEX.md**
- **Status**: ✅ Up to date
- **Purpose**: Mapping from book sections to Lean modules
- **Trust Level**: **100% - Authoritative module locations**

---

## 📝 Internal Development Notes (Historical Context)

These files document **historical development sessions** and may contain **outdated statistics** from earlier stages of the project. They are kept for historical record but are **NOT authoritative** for current statistics.

### Session Notes (Historical - May Have Old Stats):

1. **SESSION_SUMMARY.md**
   - **Purpose**: Documents the completion session
   - **Note**: Some statistics updated, but refers to historical "51/63" in places
   - **Trust**: Historical context only

2. **MULTI_APPENDIX_SUMMARY.md**
   - **Purpose**: Executive summary from multi-appendix formalization
   - **Note**: Updated with current stats, but may reference old numbers
   - **Trust**: Historical context only

3. **VERIFICATION_STATUS.md**
   - **Purpose**: Verification status report
   - **Status**: ✅ Updated with accurate current statistics
   - **Trust**: Reliable for current status

4. **PROOF_COMPLETION_SUMMARY.md**
   - **Purpose**: Documents proof completion process
   - **Note**: May reference older statistics from completion phase
   - **Trust**: Historical context only

5. **REFACTORING_SUMMARY.md**
   - **Purpose**: Documents build system refactoring
   - **Note**: May reference statistics from refactoring phase
   - **Trust**: Historical context only

6. **ACADEMIC_PAPER_OUTLINE.md**
   - **Purpose**: Draft outline for academic paper
   - **Note**: Working draft, may have old statistics
   - **Trust**: Draft only, not authoritative

7. **PAPER_INTRODUCTION.md**
   - **Purpose**: Draft paper introduction
   - **Note**: Working draft
   - **Trust**: Draft only

8. **PUBLICATION_READY_SUMMARY.md**
   - **Purpose**: Publication checklist
   - **Note**: Process documentation
   - **Trust**: Process reference only

9. **VERIFICATION_RESULTS.md**
   - **Purpose**: Build verification results from specific session
   - **Note**: Historical build verification
   - **Trust**: Historical context only

10. **PUBLISHING_INSTRUCTIONS.md**
    - **Purpose**: GitHub publication guide
    - **Note**: Process instructions
    - **Trust**: Process reference only

---

## 🔍 Audit Documentation (Transparency Records)

These files document the accuracy audit and corrections made to ensure repository credibility:

1. **ACCURACY_AUDIT.md**
   - **Purpose**: Complete audit findings
   - **Status**: Reference documentation for what was found and fixed
   - **Trust**: Audit record

2. **URGENT_CORRECTIONS_NEEDED.md**
   - **Purpose**: Action plan for corrections
   - **Status**: Completed action items
   - **Trust**: Historical record of corrections

3. **CORRECTION_SCRIPT.md**
   - **Purpose**: Detailed change instructions
   - **Status**: Implementation guide (completed)
   - **Trust**: Historical record

4. **CORRECTIONS_COMPLETED.md**
   - **Purpose**: Summary of completed corrections
   - **Status**: Final record of changes made
   - **Trust**: Completion record

---

## 📊 Current Authoritative Statistics

**For any publication, citation, or external reference, use these numbers:**

### Formalised Statements
- **Total**: 90 statements
  - **Theorems** (with proofs): 45
  - **Axioms** (without proofs): 45

### Proof Status
- **Complete proofs**: 34 theorems (76% of theorems)
- **Incomplete proofs**: 11 theorems with `sorry` (24% of theorems)

### Coverage by Appendix
- **Appendix A** (Foundations): 6/8 = 75%
- **Appendix B** (GT-SMDN): 31/31 = 100%
- **Appendix D** (Priority Flow): 8/8 = 100%
- **Appendix E** (Cascade Probability): 6/6 = 100%
- **Overall Core**: 51/55 = 93% (excluding Appendix F)

### Build Status
- **Modules**: 1,946
- **Compilation**: 100% success
- **Lean version**: 4.25.0

---

## 🎯 Quick Reference: Which File for What?

| Question | Authoritative Source |
|----------|---------------------|
| "How many theorems are formalised?" | **README.md** or **THEOREM_INVENTORY.md** |
| "Where is theorem X located?" | **THEOREM_INDEX.md** |
| "What's the proof status?" | **README.md** (Limitations section) |
| "How to cite this work?" | **CITATION.cff** or **README.md** (Citation section) |
| "What are the axioms?" | **README.md** (Limitations → Axiomatised Statements) |
| "What's the build status?" | **README.md** or CI/CD badge |
| "How was this developed?" | **SESSION_SUMMARY.md** (historical) |
| "What was the audit about?" | **ACCURACY_AUDIT.md** |

---

## 🚨 Important Notes

### Internal vs External Documentation

- **External/Public**: README.md, THEOREM_INVENTORY.md, CITATION.cff, THEOREM_INDEX.md
  - Always kept accurate and consistent
  - These are what users, reviewers, and academics will read

- **Internal/Historical**: SESSION_SUMMARY, PROOF_COMPLETION_SUMMARY, etc.
  - Document development process
  - May reference older statistics from specific sessions
  - Kept for transparency and reproducibility
  - Not intended as current reference

### Why Keep Historical Docs?

1. **Transparency**: Shows the development process
2. **Reproducibility**: Others can understand how the formalization evolved
3. **Academic Honesty**: Demonstrates iterative refinement
4. **Historical Record**: Valuable for understanding decisions made

---

## ✅ Quality Assurance

**Last consistency check**: 2025-01-17

All public-facing documentation (README.md, THEOREM_INVENTORY.md, CITATION.cff) verified to contain:
- ✅ Accurate theorem counts (90 total, 45 theorems, 45 axioms)
- ✅ Accurate proof counts (34 complete, 11 incomplete)
- ✅ Accurate appendix coverage (A: 75%, B: 100%, D: 100%, E: 100%)
- ✅ No unsubstantiated r²=0.73 claims
- ✅ Clear transparency about axioms and limitations
- ✅ Consistent British spelling throughout

---

## 📧 For Academic Review

If you're reviewing this repository for publication or citation, please:

1. **Primary sources**: Start with README.md and THEOREM_INVENTORY.md
2. **Code verification**: All code compiles with `lake build` (CI/CD confirms)
3. **Axiom transparency**: See README.md → Limitations → Axiomatised Statements
4. **Historical context**: Internal docs show development process (optional reading)

**Bottom line**: The repository is transparent about what is proven vs axiomatised, with full honesty about empirical claims and incomplete proofs.
