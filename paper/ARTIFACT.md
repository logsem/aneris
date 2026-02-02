# Artifact for the Lawyer paper

This artifact provides the technical development for the *Lawyer: Modular Obligations-Based Liveness Reasoning in Higher-Order Impredicative Concurrent Separation Logic* accepted at OOPSLA'26.

It consists of:
- Rocq formalization of all the results in the paper (described in detail in `README.md`).
- Virtual machine with pre-built formalization.
  Username/password: `lawyer`.
  All relevant files are located in `/home/lawyer/artifact`.
- Full version of the paper with appendix.


## Checking the pre-built formalization in the virtual machine

1. Install [VirtualBox](https://www.virtualbox.org/) (we used the version 7.2.4)
2. Download the `artifact.ova` file.
2. Open VirtualBox and navigate to `File/Import Appliance`. Provide the path to the downloaded `artifact.ova` and follow instructions to create a VM.
3. Run the newly created VM. 
4. Navigate to `/home/lawyer/artifact/lawyer`. 
5. Run `make -j 4` (this should terminate in a second, as the proofs are already compiled).
6. Open `check/check.v` with an editor of choice; the VM provides Emacs+Proof General and VSCode+vsrocq. 
7. Step through this file (`Next` button in Proof General, `Step Forward` button in vsrocq) until the last `Print Assumptions` line.
   Processing it might take a while, and vsrocq might appear to be stuck; wait up to a minute for it to complete.
8. The `Print Assumptions` line prints all the axioms that all the paper results (listed in `results` definition above) rely on.
   Check that only the following axioms are used:
   - `RelationalChoice.relational_choice`
   - `ClassicalUniqueChoice.dependent_unique_choice`
   - `Classical_Prop.classic`
   - `classical.PropExt`
   - `classical.FunExt`
   - `classical.Choice`
9. The file `README.md` provides a detailed description of the technical development.

## Re-building the formalization manually

- In the VM, you can run `make clean; make -j 4` in `/home/lawyer/artifact/lawyer`.
  This will rebuild the formalization of Lawyer, while keeping the rest of dependencies, including Trillium, untouched.
- Alternatively, you can rebuild the entire development from scratch, either inside VM or locally.
	For that, use the `lawyer_suppl.zip` file (in the VM, it is located in `/home/lawyer/artifact/`) and follow the installation instructions from `README.md`. 
  
