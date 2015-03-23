/**
 * Describes the different task names.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.website.toolchains.AutomtaScriptTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieBuchiAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieConcurrentTraceAbstractionTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieLassoRankerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CBuchiAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CLassoRankerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CAutomizerTC;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public class Tasks {
	/**
	 * List all toolchains that should be shown. Instantiate all toolchains,
	 * that should be shown.
	 */
	private static final Class<?>[] sToolchainTypes = { AutomtaScriptTC.class, BoogieAutomizerTC.class,
			CAutomizerTC.class, BoogieLassoRankerTC.class, CLassoRankerTC.class, BoogieBuchiAutomizerTC.class,
			CBuchiAutomizerTC.class, BoogieConcurrentTraceAbstractionTC.class };
	/**
	 * The String representations of TaskNames.
	 */
	private static final Map<TaskNames, String> sTaskStrings = new HashMap<Tasks.TaskNames, String>();
	/**
	 * Active toolchains, listed by their task(s).
	 */
	private static final Map<String, ArrayList<WebToolchain>> sActiveToolchains = new HashMap<String, ArrayList<WebToolchain>>();
	/**
	 * All generalized toolchains by their names.
	 */
	private static final Map<String, Worker> sWorkers = new HashMap<String, Worker>();

	/**
	 * @author Markus Lindenmann
	 * @author Oleksii Saukh
	 * @author Stefan Wissert
	 * @date 14.02.2012
	 */
	public enum TaskNames {
		/**
		 * Verify Boogie.
		 */
		VerifyBoogie,
		/**
		 * Verify C.
		 */
		VerifyC,

		TERMINATION_BOOGIE,

		TERMINATION_C,

		RANK_SYNTHESIS_BOOGIE,

		RANK_SYNTHESIS_C,

		/**
		 * Run automata test file.
		 */
		AUTOMATA_SCRIPT,
		/**
		 * Verify concurrent Boogie.
		 */
		VerifyConcurrentBoogie,
		/**
		 * SmtScript. Not implemented yet.
		 */
		RunSmt2Script
		// If you add something here, add a String representation to
		// initTaskNames()
		// and its supertype (worker) to
		// initWorkers() as well!
	}

	/**
	 * Getter for the string representation of task names.
	 * 
	 * @return a map of <code>TaskNames</code> to its String representation
	 */
	public static final Map<TaskNames, String> getTaskString() {
		if (sTaskStrings.isEmpty()) {
			initTaskNames();
		}
		return sTaskStrings;
	}

	/**
	 * Getter for the worker Array.
	 * 
	 * @return a map of Worker name to workers
	 */
	public final static Map<String, Worker> getWorker() {
		if (sWorkers.isEmpty()) {
			initWorkers();
		}
		return sWorkers;
	}

	/**
	 * Get the corresponding syntax highlighter for this task.
	 * 
	 * @param taskName
	 *            the task name
	 * @return the SyntaxHighlighter to use
	 */
	public static final String getSyntaxHighlightingMode(String taskName) {
		try {
			TaskNames name = TaskNames.valueOf(taskName);
			// TODO : check if the js file exists...
			switch (name) {
			// case AUTOMATA_SCRIPT:
			// return "ats";
			// case RunSmt2Script:
			// return "smt2";
			case VerifyBoogie:
			case TERMINATION_BOOGIE:
			case RANK_SYNTHESIS_BOOGIE:
			case VerifyConcurrentBoogie:
				return "boogie";
			case VerifyC:
			case TERMINATION_C:
			case RANK_SYNTHESIS_C:
				return "c_cpp";
			default:
				return "text";
			}
		} catch (IllegalArgumentException e) {
			return "text";
		}
	}

	/**
	 * Getter for active toolchains.
	 * 
	 * @return a list of toolchains, that should be displayed on the website.
	 */
	public final static Map<String, ArrayList<WebToolchain>> getActiveToolchains() {
		if (sActiveToolchains.isEmpty()) {
			initToolchains();
		}
		return sActiveToolchains;
	}

	/**
	 * Initializes the workers mapping
	 */
	private static void initWorkers() {
		SimpleLogger.log("Initializing workers...");

		String description, name;

		name = BoogieAutomizerTC.s_Automizer;
		description = "Implementation of our automata-theoretic approach to software verification.";
		Worker w = new Worker(name, "verify", description, null);
		w.setLogoURL("img/tool_logo.png");
		sWorkers.put(w.getId(), w);

		name = "Concurrent Trace Abstraction";
		description = null;
		w = new Worker(name, "verify", description, null);
		sWorkers.put(w.getId(), w);

		name = "Büchi Automizer";
		description = "This is a new approach for termination analysis based on Büchi automata.";
		w = new Worker(name, "analyze", description, null);
		sWorkers.put(w.getId(), w);

		name = "LTL Automizer";
		description = "An LTL software model checker based on separation of (in)feasibility and (non-)termination proofs.";
		w = new Worker(name, "analyze", description, null);
		sWorkers.put(w.getId(), w);

		name = "Lasso Ranker";
		description = "This is to synthesize ranking functions of lasso programs.";
		w = new Worker(name, "rank", description, null);
		// w.setInterfaceLayoutFontsize("40"); // sample for overwriting
		// fontsize setting
		// w.setInterfaceLayoutOrientation("vertical"); // sample for
		// overwriting orientation setting
		// w.setInterfaceLayoutTransitions("false"); // sample for overwriting
		// animations setting
		// w.setContentURL("http://localhost:8080/Website/json/lasso_ranker.json");
		// // sample for setting an optional url
		sWorkers.put(w.getId(), w);

		name = "Automata Script";
		description = null;
		w = new Worker(name, "run", description, null);
		w.setUserInfo(""); // sample user information, being shown on Automata
							// Script page
		sWorkers.put(w.getId(), w);

		completeInitWorker();

	}

	/**
	 * Adds toolchains automatically to worker array
	 */
	private static void completeInitWorker() {
		for (Map.Entry<String, ArrayList<WebToolchain>> tcPair : getActiveToolchains().entrySet()) {
			for (WebToolchain toolchain : tcPair.getValue()) {
				if (!sWorkers.containsKey(Worker.toKey(toolchain.getName()))) {
					sWorkers.put(Worker.toKey(toolchain.getName()), new Worker(toolchain.getName(), null, null, null));
					SimpleLogger.log("Added worker for toolchain " + toolchain.getName());
				}
				sWorkers.get(Worker.toKey(toolchain.getName())).addToolchain(toolchain);
			}
		}
		SimpleLogger.log("Finished initializing workers");
		SimpleLogger.log("The following " + sWorkers.size() + " workers are present:");
		for (Entry<String, Worker> worker : sWorkers.entrySet()) {
			SimpleLogger.log(worker.getKey());
		}
	}

	/**
	 * Initializes the task name mapping.
	 */
	private static void initTaskNames() {
		SimpleLogger.log("Initializing task names...");

		// String should have at most 30 chars and must not be empty!
		sTaskStrings.put(TaskNames.AUTOMATA_SCRIPT, "Run Automata Script");
		sTaskStrings.put(TaskNames.RunSmt2Script, "Run Smt2Script (not yet available)");
		sTaskStrings.put(TaskNames.VerifyBoogie, "Verify Boogie");
		sTaskStrings.put(TaskNames.VerifyC, "Verify C");
		sTaskStrings.put(TaskNames.TERMINATION_BOOGIE, "Analyze Termination Boogie");
		sTaskStrings.put(TaskNames.TERMINATION_C, "Analyze Termination C");
		sTaskStrings.put(TaskNames.RANK_SYNTHESIS_BOOGIE, "Synthesize ranking function Boogie");
		sTaskStrings.put(TaskNames.RANK_SYNTHESIS_C, "Synthesize ranking function C");
		sTaskStrings.put(TaskNames.VerifyConcurrentBoogie, "Verify concurrent Boogie");

		SimpleLogger.log("Finished initializing task names");
		SimpleLogger.log("The following " + sTaskStrings.size() + " task names are present:");
		for (Entry<TaskNames, String> entry : sTaskStrings.entrySet()) {
			SimpleLogger.log(entry.getKey());
		}
	}

	private static void initToolchains() {
		SimpleLogger.log("Initializing toolchains...");
		for (Class<?> toolchainType : sToolchainTypes) {
			WebToolchain tc;
			try {
				tc = (WebToolchain) toolchainType.getConstructor().newInstance((Object[]) null);
				for (TaskNames taskName : tc.getTaskName()) {
					if (!sActiveToolchains.containsKey(taskName.toString())) {
						sActiveToolchains.put(taskName.toString(), new ArrayList<WebToolchain>());
						SimpleLogger.log("Added toolchain " + tc.getId() + " to task " + taskName.toString());
					}
					sActiveToolchains.get(taskName.toString()).add(tc);
				}
			} catch (Exception e) {
				SimpleLogger.log("An exception occured during initialization of toolchain "
						+ toolchainType.getCanonicalName());
				SimpleLogger.log(e.getCause());
			}
		}
		SimpleLogger.log("Finished initializing toolchains");
	}
}
