/**
 * Describes the different task names.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.website.toolchains.AutomtaScriptTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieBuchiAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieConcurrentTraceAbstractionTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieKojakTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieLassoRankerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieTaipanTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CBuchiAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CKojakTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CLTLAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CLassoRankerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CTaipanTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.NameStrings;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public class Tasks {
	/**
	 * List all toolchains that should be shown. Instantiate all toolchains, that should be shown.
	 */
	private static final Class<?>[] sToolchainTypes = { AutomtaScriptTC.class, BoogieAutomizerTC.class,
	        CAutomizerTC.class, BoogieLassoRankerTC.class, CLassoRankerTC.class, BoogieBuchiAutomizerTC.class,
	        CBuchiAutomizerTC.class, BoogieConcurrentTraceAbstractionTC.class, CLTLAutomizerTC.class, CKojakTC.class,
	        BoogieKojakTC.class, CTaipanTC.class, BoogieTaipanTC.class };
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
		AUTOMIZER_BOOGIE, AUTOMIZER_C,

		TERMINATION_BOOGIE, TERMINATION_C,

		RANK_SYNTHESIS_BOOGIE, RANK_SYNTHESIS_C,

		AUTOMATA_SCRIPT,

		CONCURRENT_TRACE_ABSTRACTION_BOOGIE,

		LTLAUTOMIZER_C, KOJAK_C, KOJAK_BOOGIE,

		TAIPAN_C, TAIPAN_BOOGIE,

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
		SimpleLogger.log("returning " + sWorkers.size() + " workers");
		for (final Entry<String, Worker> entry : sWorkers.entrySet()) {
			SimpleLogger.log("Woker name " + entry.getKey() + " " + entry.getValue());
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
	public static final String getSyntaxHighlightingMode(final String taskName) {
		try {
			final TaskNames name = TaskNames.valueOf(taskName);
			// TODO : check if the js file exists...
			switch (name) {
			// case AUTOMATA_SCRIPT:
			// return "ats";
			// case RunSmt2Script:
			// return "smt2";
			case AUTOMIZER_BOOGIE:
			case TERMINATION_BOOGIE:
			case RANK_SYNTHESIS_BOOGIE:
			case CONCURRENT_TRACE_ABSTRACTION_BOOGIE:
			case KOJAK_BOOGIE:
			case TAIPAN_BOOGIE:
				return "boogie";
			case AUTOMIZER_C:
			case TERMINATION_C:
			case RANK_SYNTHESIS_C:
			case LTLAUTOMIZER_C:
			case KOJAK_C:
			case TAIPAN_C:
				return "c_cpp";
			default:
				return "text";
			}
		} catch (final IllegalArgumentException e) {
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

		name = NameStrings.s_TOOL_Automizer;
		description = NameStrings.s_DESCRIPTION_Automizer;
		Worker w = new Worker(name, NameStrings.s_TASK_verify, description, null);
		w.setLogoURL("img/tool_logo.png");
		sWorkers.put(w.getId(), w);

		name = NameStrings.s_TOOL_AutomizerConcurrent;
		description = NameStrings.s_DESCRIPTION_AutomizerConcurrent;
		w = new Worker(name, NameStrings.s_TASK_verify, description, null);
		sWorkers.put(w.getId(), w);

		name = NameStrings.s_TOOL_BuchiAutomizer;
		description = NameStrings.s_DESCRIPTION_BuchiAutomizer;
		w = new Worker(name, NameStrings.s_TASK_analyze, description, null);
		sWorkers.put(w.getId(), w);

		name = "LTL Automizer";
		description = "An LTL software model checker based on Büchi programs.";
		w = new Worker(name, NameStrings.s_TASK_verify, description, null);
		sWorkers.put(w.getId(), w);

		name = "Kojak";
		description = "A software model checker";
		w = new Worker(name, NameStrings.s_TASK_verify, description, null);
		sWorkers.put(w.getId(), w);

		name = NameStrings.s_TOOL_LassoRanker;
		description = NameStrings.s_DESCRIPTION_LassoRanker;
		w = new Worker(name, NameStrings.s_TASK_synthesize, description, null);
		// w.setInterfaceLayoutFontsize("40"); // sample for overwriting
		// fontsize setting
		// w.setInterfaceLayoutOrientation("vertical"); // sample for
		// overwriting orientation setting
		// w.setInterfaceLayoutTransitions("false"); // sample for overwriting
		// animations setting
		// w.setContentURL("http://localhost:8080/Website/json/lasso_ranker.json");
		// // sample for setting an optional url
		sWorkers.put(w.getId(), w);

		name = NameStrings.s_TOOL_AutomataScriptInterpreter;
		description = NameStrings.s_DESCRIPTION_AutomataScriptInterpreter;
		w = new Worker(name, NameStrings.s_TASK_run, description, null);
		w.setUserInfo(""); // sample user information, being shown on Automata
		                   // Script page
		sWorkers.put(w.getId(), w);

		name = NameStrings.s_TOOL_Taipan;
		description = NameStrings.s_DESCRIPTION_Taipan;
		w = new Worker(name, NameStrings.s_TASK_analyze, description, null);
		sWorkers.put(w.getId(), w);

		completeInitWorker();

	}

	/**
	 * Adds toolchains automatically to worker array
	 */
	private static void completeInitWorker() {
		for (final Map.Entry<String, ArrayList<WebToolchain>> tcPair : getActiveToolchains().entrySet()) {
			for (final WebToolchain toolchain : tcPair.getValue()) {
				if (!sWorkers.containsKey(Worker.toKey(toolchain.getName()))) {
					SimpleLogger.log("Worker for toolchain " + toolchain.getName()
					        + " missing! Adding a worker via a very strange workaround");
					sWorkers.put(Worker.toKey(toolchain.getName()), new Worker(toolchain.getName(), null, null, null));
					SimpleLogger.log("Added worker for toolchain " + toolchain.getName());
				}
				sWorkers.get(Worker.toKey(toolchain.getName())).addToolchain(toolchain);
			}
		}
		SimpleLogger.log("Finished initializing workers");
		SimpleLogger.log("The following " + sWorkers.size() + " workers are present:");
		for (final Entry<String, Worker> worker : sWorkers.entrySet()) {
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
		sTaskStrings.put(TaskNames.AUTOMIZER_BOOGIE, "Verify Boogie");
		sTaskStrings.put(TaskNames.AUTOMIZER_C, "Verify C");
		sTaskStrings.put(TaskNames.TERMINATION_BOOGIE, "Analyze Termination Boogie");
		sTaskStrings.put(TaskNames.TERMINATION_C, "Analyze Termination C");
		sTaskStrings.put(TaskNames.RANK_SYNTHESIS_BOOGIE, "Synthesize ranking function Boogie");
		sTaskStrings.put(TaskNames.RANK_SYNTHESIS_C, "Synthesize ranking function C");
		sTaskStrings.put(TaskNames.CONCURRENT_TRACE_ABSTRACTION_BOOGIE, "Verify concurrent Boogie");
		sTaskStrings.put(TaskNames.LTLAUTOMIZER_C, "Verify if C program fulfils LTL property");
		sTaskStrings.put(TaskNames.KOJAK_C, "Verify C");
		sTaskStrings.put(TaskNames.KOJAK_BOOGIE, "Verify Boogie");
		sTaskStrings.put(TaskNames.TAIPAN_C, "Verify C");
		sTaskStrings.put(TaskNames.TAIPAN_BOOGIE, "Verify Boogie");

		SimpleLogger.log("Finished initializing task names");
		SimpleLogger.log("The following " + sTaskStrings.size() + " task names are present:");
		for (final Entry<TaskNames, String> entry : sTaskStrings.entrySet()) {
			SimpleLogger.log(entry.getKey());
		}
	}

	private static void initToolchains() {
		SimpleLogger.log("Initializing toolchains...");
		for (final Class<?> toolchainType : sToolchainTypes) {
			WebToolchain tc;
			try {
				tc = (WebToolchain) toolchainType.getConstructor().newInstance((Object[]) null);
				for (final TaskNames taskName : tc.getTaskName()) {
					if (!sActiveToolchains.containsKey(taskName.toString())) {
						sActiveToolchains.put(taskName.toString(), new ArrayList<WebToolchain>());
						SimpleLogger.log("Added toolchain " + tc.getId() + " to task " + taskName.toString());
					}
					sActiveToolchains.get(taskName.toString()).add(tc);
				}
			} catch (final Exception e) {
				SimpleLogger.log(
				        "An exception occured during initialization of toolchain " + toolchainType.getCanonicalName());
				SimpleLogger.log(e.getCause());
			}
		}
		SimpleLogger.log("Finished initializing toolchains");
	}
}
