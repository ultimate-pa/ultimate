/**
 * Describes the different task names.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.EnumMap;
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
	private static final Class<?>[] TOOLCHAIN_TYPES = {
			//@formatter:off
			AutomtaScriptTC.class,
			BoogieAutomizerTC.class,
			CAutomizerTC.class,
			BoogieLassoRankerTC.class,
			CLassoRankerTC.class,
			BoogieBuchiAutomizerTC.class,
			CBuchiAutomizerTC.class,
			BoogieConcurrentTraceAbstractionTC.class,
			CLTLAutomizerTC.class,
			CKojakTC.class,
			BoogieKojakTC.class,
			CTaipanTC.class,
			BoogieTaipanTC.class
			//@formatter:on
	};
	/**
	 * The String representations of TaskNames.
	 */
	private static final Map<TaskNames, String> TASK_STRINGS = new EnumMap<>(TaskNames.class);
	/**
	 * Active toolchains, listed by their task(s).
	 */
	private static final Map<String, ArrayList<WebToolchain>> ACTIVE_TOOLCHAINS = new HashMap<>();
	/**
	 * All generalized toolchains by their names.
	 */
	private static final Map<String, Worker> WORKERS = new HashMap<>();

	/**
	 * @author Markus Lindenmann
	 * @author Oleksii Saukh
	 * @author Stefan Wissert
	 * @date 14.02.2012
	 */
	public enum TaskNames {
		AUTOMIZER_BOOGIE,

		AUTOMIZER_C,

		TERMINATION_BOOGIE,

		TERMINATION_C,

		RANK_SYNTHESIS_BOOGIE,

		RANK_SYNTHESIS_C,

		AUTOMATA_SCRIPT,

		CONCURRENT_TRACE_ABSTRACTION_BOOGIE,

		LTLAUTOMIZER_C,

		KOJAK_C,

		KOJAK_BOOGIE,

		TAIPAN_C,

		TAIPAN_BOOGIE

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
		if (TASK_STRINGS.isEmpty()) {
			initTaskNames();
		}
		return TASK_STRINGS;
	}

	/**
	 * Getter for the worker Array.
	 *
	 * @return a map of Worker name to workers
	 */
	public static final Map<String, Worker> getWorker() {
		if (WORKERS.isEmpty()) {
			initWorkers();
		}
		SimpleLogger.log("returning " + WORKERS.size() + " workers");
		for (final Entry<String, Worker> entry : WORKERS.entrySet()) {
			SimpleLogger.log("Woker name " + entry.getKey() + " " + entry.getValue());
		}
		return WORKERS;
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
			SimpleLogger.log("taskName " + taskName + " is not known, using \"text\"");
			return "text";
		}
	}

	/**
	 * Getter for active toolchains.
	 *
	 * @return a list of toolchains, that should be displayed on the website.
	 */
	public static final Map<String, ArrayList<WebToolchain>> getActiveToolchains() {
		if (ACTIVE_TOOLCHAINS.isEmpty()) {
			initToolchains();
		}
		return ACTIVE_TOOLCHAINS;
	}

	/**
	 * Initializes the workers mapping
	 */
	private static void initWorkers() {
		SimpleLogger.log("Initializing workers...");

		String description, name;

		name = NameStrings.TOOL_AUTOMIZER;
		description = NameStrings.DESCRIPTION_AUTOMIZER;
		Worker w = new Worker(name, NameStrings.TASK_VERIFY, description, null);
		w.setLogoURL("img/tool_logo.png");
		WORKERS.put(w.getId(), w);

		name = NameStrings.TOOL_AUTOMIZER_CONCURRENT;
		description = NameStrings.DESCRIPTION_AUTOMIZER_CONCURRENT;
		w = new Worker(name, NameStrings.TASK_VERIFY, description, null);
		WORKERS.put(w.getId(), w);

		name = NameStrings.TOOL_AUTOMIZER_BUCHI;
		description = NameStrings.DESCRIPTION_AUTOMIZER_BUCHI;
		w = new Worker(name, NameStrings.TASK_ANALYZE, description, null);
		WORKERS.put(w.getId(), w);

		name = "LTL Automizer";
		description = "An LTL software model checker based on Büchi programs.";
		w = new Worker(name, NameStrings.TASK_VERIFY, description, null);
		WORKERS.put(w.getId(), w);

		name = "Kojak";
		description = "A software model checker";
		w = new Worker(name, NameStrings.TASK_VERIFY, description, null);
		WORKERS.put(w.getId(), w);

		name = NameStrings.TOOL_LASSO_RANKER;
		description = NameStrings.DESCRIPTION_LASSO_RANKER;
		w = new Worker(name, NameStrings.TASK_SYNTHESIZE, description, null);
		// w.setInterfaceLayoutFontsize("40"); // sample for overwriting
		// fontsize setting
		// w.setInterfaceLayoutOrientation("vertical"); // sample for
		// overwriting orientation setting
		// w.setInterfaceLayoutTransitions("false"); // sample for overwriting
		// animations setting
		// w.setContentURL("http://localhost:8080/Website/json/lasso_ranker.json");
		// // sample for setting an optional url
		WORKERS.put(w.getId(), w);

		name = NameStrings.TOOL_AUTOMATA_SCRIPT_INTERPRETER;
		description = NameStrings.DESCRIPTION_AUTOMATA_SCRIPT_INTERPRETER;
		w = new Worker(name, NameStrings.TASK_RUN, description, null);
		w.setUserInfo(""); // sample user information, being shown on Automata
							// Script page
		WORKERS.put(w.getId(), w);

		completeInitWorker();

	}

	/**
	 * Adds toolchains automatically to worker array
	 */
	private static void completeInitWorker() {
		for (final Map.Entry<String, ArrayList<WebToolchain>> tcPair : getActiveToolchains().entrySet()) {
			for (final WebToolchain toolchain : tcPair.getValue()) {
				if (!WORKERS.containsKey(Worker.toKey(toolchain.getName()))) {
					SimpleLogger.log("Worker for toolchain " + toolchain.getName()
							+ " missing! Adding a worker via a very strange workaround");
					WORKERS.put(Worker.toKey(toolchain.getName()), new Worker(toolchain.getName(), null, null, null));
					SimpleLogger.log("Added worker for toolchain " + toolchain.getName());
				}
				WORKERS.get(Worker.toKey(toolchain.getName())).addToolchain(toolchain);
			}
		}
		SimpleLogger.log("Finished initializing workers");
		SimpleLogger.log("The following " + WORKERS.size() + " workers are present:");
		for (final Entry<String, Worker> worker : WORKERS.entrySet()) {
			SimpleLogger.log(worker.getKey());
		}
	}

	/**
	 * Initializes the task name mapping.
	 */
	private static void initTaskNames() {
		SimpleLogger.log("Initializing task names...");

		// String should have at most 30 chars and must not be empty!
		TASK_STRINGS.put(TaskNames.AUTOMATA_SCRIPT, "Run Automata Script");
		TASK_STRINGS.put(TaskNames.AUTOMIZER_BOOGIE, "Verify Boogie");
		TASK_STRINGS.put(TaskNames.AUTOMIZER_C, "Verify C");
		TASK_STRINGS.put(TaskNames.TERMINATION_BOOGIE, "Analyze Termination Boogie");
		TASK_STRINGS.put(TaskNames.TERMINATION_C, "Analyze Termination C");
		TASK_STRINGS.put(TaskNames.RANK_SYNTHESIS_BOOGIE, "Synthesize ranking function Boogie");
		TASK_STRINGS.put(TaskNames.RANK_SYNTHESIS_C, "Synthesize ranking function C");
		TASK_STRINGS.put(TaskNames.CONCURRENT_TRACE_ABSTRACTION_BOOGIE, "Verify concurrent Boogie");
		TASK_STRINGS.put(TaskNames.LTLAUTOMIZER_C, "Verify if C program fulfils LTL property");
		TASK_STRINGS.put(TaskNames.KOJAK_C, "Verify C");
		TASK_STRINGS.put(TaskNames.KOJAK_BOOGIE, "Verify Boogie");

		SimpleLogger.log("Finished initializing task names");
		SimpleLogger.log("The following " + TASK_STRINGS.size() + " task names are present:");
		for (final Entry<TaskNames, String> entry : TASK_STRINGS.entrySet()) {
			SimpleLogger.log(entry.getKey());
		}
	}

	private static void initToolchains() {
		SimpleLogger.log("Initializing toolchains...");
		for (final Class<?> toolchainType : TOOLCHAIN_TYPES) {
			WebToolchain tc;
			try {
				tc = (WebToolchain) toolchainType.getConstructor().newInstance((Object[]) null);
				for (final TaskNames taskName : tc.getTaskName()) {
					if (!ACTIVE_TOOLCHAINS.containsKey(taskName.toString())) {
						ACTIVE_TOOLCHAINS.put(taskName.toString(), new ArrayList<WebToolchain>());
						SimpleLogger.log("Added toolchain " + tc.getId() + " to task " + taskName.toString());
					}
					ACTIVE_TOOLCHAINS.get(taskName.toString()).add(tc);
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
