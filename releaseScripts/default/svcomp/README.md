# Participation
SVCOMP becomes more complex every year. Hence, this README will try to outline the steps necessary to participate with
Ultimate in the competition.

<https://sv-comp.sosy-lab.org/2025/submission.php> contains a first overview:
1. Register tools with Easychair. Only title and authors are required, the first author is the jury member, i.e., the
   main contact for the tool.
2. The tool submission (this README is about that submission)
3. If you want to publish, a 4 page system description. This is usually later in the process.

<https://sv-comp.sosy-lab.org/2025/dates.php> is the timeline, which is usually like this:
* Oct : register tools with Easychair
* +1w : benchmark submission deadline
* +1w : initial tool submission deadline
* +1w : benchmark freeze (no more merges)
* +3w : tool reviews / qualification notification
* +1w : final tool submission deadline
* +2w : internal competition results notification
* +1w : public competition results notification
* +3w : system description / paper deadline
* +4w : paper notification
* +1w : camera-ready deadline

## Tool Submission
**Note**: we use https for all repositories in this README, but it is much more convenient for you to use SSH to
actually work with them.

1. Prepare by creating a new Ultimate version (at least increment patch, i.e., go from 0.2.4 to 0.2.5) using
   `makeRelease.sh`. You should not upload anything to GitHub at that stage.

2. Run internal fast prerun with at least Automizer
   * 120s, 8GB, 2 cores are good resource limits, takes around 24h
   * You need the latest ``uautomizer.xml`` from
     <https://gitlab.com/sosy-lab/sv-comp/bench-defs> and the latest benchexec from
     <https://github.com/sosy-lab/benchexec>.

     Update our forks of these repositories while you are at it:
     * <https://gitlab.com/ultimate-pa/sv-benchmarks>
     * <https://github.com/ultimate-pa/benchexec>
   * Adapt the resource usage, ensure that `--full-output` is set, remove hardware restrictions.

3. Ensure that all tools have a complete description in the `fm-tools` repository
   (<https://gitlab.com/sosy-lab/benchmarking/fm-tools>).

   This requires an Zenodo DOI for the tool, and a benchmark definition in the `bench-defs` repository
   (<https://gitlab.com/sosy-lab/sv-comp/bench-defs>), and a tool-info module in the benchexec repository.

   **Build Ultimate**
   1. Create a fresh Ultimate build for all tools using `./makeFresh.sh`
   2. Ensure that the tools have a version without `-m`, meaning the repo must not contain modification or untracked
      files (!). Use a clean git worktree if necessary.

   **Ensure benchexec tool-info module**
   If you have a new tool, you need to add a tool-info module to the benchexec repository.
   <https://github.com/sosy-lab/benchexec/blob/main/doc/tool-integration.md> describes the process.
   If you are unsure, test with  
   `PYTHONPATH=<path-to-benchexec> python3 -m benchexec.test_tool_info --debug --tool-directory <path-to-tool> --no-container  <name-of-toolinfo-module>`  
   If your tool is based on Ultimate, you should copy the latest Ultimate tool and adapt the text.
   <https://github.com/sosy-lab/benchexec/blob/main/benchexec/tools/ultimategemcutter.py> is currently the latest.

   **Update bench-defs**
   1. Checkout our fm-tools form <https://gitlab.com/ultimate-pa/sv-benchmarks> and sync it with
      upstream (add new remote `upstream` for <https://gitlab.com/sosy-lab/sv-comp/bench-defs>).
   2. Create a new branch for your change.

   **Update fm-tools**
   1. Checkout our fm-tools fork <https://gitlab.com/ultimate-pa/fm-tools> and sync it with
      upstream (add new remote `upstream` for <https://gitlab.com/sosy-lab/benchmarking/fm-tools>).
   2. Create a new branch for your submission.
   3. Ensure that existing files in `data/` are up-to-date wrt. metadata (everything except the DOI).
   4. Add new tool without Zenodo if necessary, commit.
   5. Ensure that `releaseScripts/default/svcomp/upload_zenodo.py` from ``releaseScripts/default`` 
      * contains all tools you want to submit (.zip location and fm-tools .yml location), and
      * uses the correct metadata for Zenodo itself (authors, strings, etc).
   6. Use `upload_zenodo.py` to upload the .zips to Zenodo, using metadata from the fm-tools .yml file. This will
      generate a DOI for each tool and modify the .yml file.
   7. Commit new DOI in fm-tools.
   8. Push and file MR.
