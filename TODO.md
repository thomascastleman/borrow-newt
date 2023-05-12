# To do

- [ ] Optimizations for efficiency

- [ ] Splitting everything into multiple .frg files based on the comments dividing functionality

- [ ] Try very large instances

  - 15 Statement ran for an hour without any results
  - Try 10 Statement? 11?

- [x] Visualization

  - [x] Add flag for removing indentation + explicit braces from scope of `let` statements
  - [x] Line numbers in visualization

- [x] Testing
  - [x] Owned value is created in inner scope and lives into outer scope is sat
  - [x] Try to verify no dangling pointers under borrow checking

# Efficiency

## (**OLD**) Valid + Borrow Checks

exactly 7 Statement, exactly 3 Variable, exactly 3 Value, 5 Type: 43 seconds translation, 5 seconds solving

exactly 8 Statement, exactly 3 Variable, exactly 3 Value, 5 Type, 5 Int: 40 seconds translation, 995 ms solving

8 Statement, 5 Variable, 5 Value, 5 Type: 8 min translation, 311ms solving

9 Statement, 5 Variable, 5 Value, 5 Type: 23 min translation, 2 seconds solving

- With Tim's optimizer, down to 15 min translation, 560ms solving

## Valid **with new end of lifetime constraints**

exactly 7 Statement, exactly 3 Variable, exactly 3 Value, 5 Type: 3.5 min translation, 5 seconds solving

exactly 8 Statement, exactly 3 Variable, exactly 3 Value, 5 Type: 3.5 min translation, 12 seconds solving

for exactly 8 Statement, exactly 4 Variable, exactly 4 Value, 5 Type, 5 Int
with triple borrow: 10 min translation, 30 sec solving

## Test Results

```
❯ date && racket borrowcheck.test.frg
Thu May 11 03:36:38 PM EDT 2023
Warning: /home/tc/Desktop/courses/1710/projects/csci1710-final/borrowcheck.test.frg 61:4 Test does not reference satisfiesBorrowChecking.
Forge version: 2.8.0
To report issues with Forge, please visit https://report.forge-fm.org
#vars: (size-variables 63369); #primary: (size-primary 545); #clauses: (size-clauses 172937)
Transl (ms): (time-translation 105022); Solving (ms): (time-solving 43570)
#vars: (size-variables 63422); #primary: (size-primary 545); #clauses: (size-clauses 173136)
Transl (ms): (time-translation 124003); Solving (ms): (time-solving 69441) Core min (ms): (time-core 0)
#vars: (size-variables 63815); #primary: (size-primary 548); #clauses: (size-clauses 174176)
Transl (ms): (time-translation 112459); Solving (ms): (time-solving 5002)
#vars: (size-variables 63813); #primary: (size-primary 548); #clauses: (size-clauses 174387)
Transl (ms): (time-translation 111899); Solving (ms): (time-solving 58919) Core min (ms): (time-core 0)
#vars: (size-variables 64601); #primary: (size-primary 552); #clauses: (size-clauses 175688)
Transl (ms): (time-translation 111861); Solving (ms): (time-solving 4035)
#vars: (size-variables 64599); #primary: (size-primary 552); #clauses: (size-clauses 175899)
Transl (ms): (time-translation 112385); Solving (ms): (time-solving 93432) Core min (ms): (time-core 0)
#vars: (size-variables 62935); #primary: (size-primary 548); #clauses: (size-clauses 171810)
Transl (ms): (time-translation 110678); Solving (ms): (time-solving 12127)
#vars: (size-variables 62933); #primary: (size-primary 548); #clauses: (size-clauses 172021)
Transl (ms): (time-translation 112261); Solving (ms): (time-solving 48415) Core min (ms): (time-core 0)
#vars: (size-variables 65582); #primary: (size-primary 563); #clauses: (size-clauses 178751)
Transl (ms): (time-translation 113815); Solving (ms): (time-solving 97746) Core min (ms): (time-core 0)

❯ date && racket lifetimes.test.frg
Thu May 11 04:01:24 PM EDT 2023
Forge version: 2.8.0
To report issues with Forge, please visit https://report.forge-fm.org
#vars: (size-variables 57235); #primary: (size-primary 537); #clauses: (size-clauses 157322)
Transl (ms): (time-translation 103068); Solving (ms): (time-solving 373)
#vars: (size-variables 57586); #primary: (size-primary 541); #clauses: (size-clauses 158057)
Transl (ms): (time-translation 105016); Solving (ms): (time-solving 11054) Core min (ms): (time-core 0)
#vars: (size-variables 58797); #primary: (size-primary 548); #clauses: (size-clauses 161062)
Transl (ms): (time-translation 103502); Solving (ms): (time-solving 17448) Core min (ms): (time-core 0)
#vars: (size-variables 57368); #primary: (size-primary 541); #clauses: (size-clauses 157535)
Transl (ms): (time-translation 103244); Solving (ms): (time-solving 248)
#vars: (size-variables 59492); #primary: (size-primary 563); #clauses: (size-clauses 162895)
Transl (ms): (time-translation 104619); Solving (ms): (time-solving 67237) Core min (ms): (time-core 0)

❯ date && racket structure.test.frg
Thu May 11 04:13:14 PM EDT 2023
Forge version: 2.8.0
To report issues with Forge, please visit https://report.forge-fm.org
#vars: (size-variables 0); #primary: (size-primary 0); #clauses: (size-clauses 0)
Transl (ms): (time-translation 4145); Solving (ms): (time-solving 0) Core min (ms): (time-core 0)
#vars: (size-variables 29875); #primary: (size-primary 551); #clauses: (size-clauses 77286)
Transl (ms): (time-translation 2757); Solving (ms): (time-solving 7381) Core min (ms): (time-core 0)
#vars: (size-variables 29961); #primary: (size-primary 558); #clauses: (size-clauses 77780)
Transl (ms): (time-translation 2658); Solving (ms): (time-solving 8444) Core min (ms): (time-core 0)
#vars: (size-variables 29343); #primary: (size-primary 537); #clauses: (size-clauses 76240)
Transl (ms): (time-translation 2512); Solving (ms): (time-solving 70)
#vars: (size-variables 30038); #primary: (size-primary 551); #clauses: (size-clauses 77932)
Transl (ms): (time-translation 2368); Solving (ms): (time-solving 31753) Core min (ms): (time-core 0)
#vars: (size-variables 29883); #primary: (size-primary 548); #clauses: (size-clauses 77524)
Transl (ms): (time-translation 2505); Solving (ms): (time-solving 1682) Core min (ms): (time-core 0)
#vars: (size-variables 29507); #primary: (size-primary 551); #clauses: (size-clauses 76526)
Transl (ms): (time-translation 2285); Solving (ms): (time-solving 1297) Core min (ms): (time-core 0)
#vars: (size-variables 29410); #primary: (size-primary 544); #clauses: (size-clauses 76352)
Transl (ms): (time-translation 2272); Solving (ms): (time-solving 78) Core min (ms): (time-core 0)
#vars: (size-variables 29398); #primary: (size-primary 541); #clauses: (size-clauses 76328)
Transl (ms): (time-translation 2321); Solving (ms): (time-solving 86) Core min (ms): (time-core 0)
#vars: (size-variables 29448); #primary: (size-primary 541); #clauses: (size-clauses 76411)
Transl (ms): (time-translation 2314); Solving (ms): (time-solving 4) Core min (ms): (time-core 0)
#vars: (size-variables 29552); #primary: (size-primary 549); #clauses: (size-clauses 76654)
Transl (ms): (time-translation 2404); Solving (ms): (time-solving 49)
#vars: (size-variables 30016); #primary: (size-primary 559); #clauses: (size-clauses 77588)
Transl (ms): (time-translation 2376); Solving (ms): (time-solving 62949) Core min (ms): (time-core 0
```

# Bugs

# Questions

- Is there a way to parameterize over the bounds (exactly 5 Statement, etc)
  in tests? That way we can easily change the bounds on all our tests instead
  of manually rewriting for each test.
