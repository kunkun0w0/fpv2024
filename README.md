# Brown CS 1951x: Zekun's Final Project
## Deterministic Finite Automaton Minimization

In this repository, you'll find zekun's final project in `LoVe/Homework/FinalProject.lean`

The project contains:
1. Basic definitions of DFA.
2. Myhill-Nerode equivalence
3. States Partitioning
4. DFA Minimization

## Using this repository

This repository is a [Lean project](https://leanprover-community.github.io/install/project.html).
There are some basic steps you should take at the beginning to set it up.
These only need to be done once.
If and when you need to create any new `.lean` files,
create them in the `src` directory of this project,
to ensure that all your expected imports are available.

### Setup

We assume that you have installed:
* `git`
* `lean` (via `elan`)
* VSCode and the Lean extension

following our [course setup instructions](https://browncs1951x.github.io/setup.html).

    
To set up this project, run:

```bash
git clone https://github.com/BrownCS1951x/fpv2024.git
cd fpv2024
lake exe cache get 
lake build LoVe.LoVelib
```

When you open VSCode, make sure that you use the **Open Folder** feature
to open the entire `fpv2024` directory,
instead of opening individual files. 
The easiest way to do this is from the command line:
```bash
cd fpv2024
code .
```
But `File -> Open Folder...` works fine too.

