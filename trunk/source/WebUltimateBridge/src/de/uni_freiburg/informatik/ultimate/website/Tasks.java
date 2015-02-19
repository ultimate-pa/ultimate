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
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieTraceAbstractionTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CBuchiAutomizerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CLassoRankerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.CTraceAbstractionTC;

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
	@SuppressWarnings("rawtypes")
	private static final Class[] sActToolchains =
						{
							AutomtaScriptTC.class, 
							BoogieTraceAbstractionTC.class,
							CTraceAbstractionTC.class,
							BoogieLassoRankerTC.class, 
							CLassoRankerTC.class,
							BoogieBuchiAutomizerTC.class,
							CBuchiAutomizerTC.class,
							BoogieConcurrentTraceAbstractionTC.class
						};
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
	 * Initializes the task name mapping.
	 */
	private static void initTaskNames() {
		// String should have at most 30 chars and must not be empty!
		sTaskStrings.put(TaskNames.AUTOMATA_SCRIPT,        "Run Automata Script");
		sTaskStrings.put(TaskNames.RunSmt2Script,          "Run Smt2Script (not yet available)");
		sTaskStrings.put(TaskNames.VerifyBoogie, 	       "Verify Boogie");
		sTaskStrings.put(TaskNames.VerifyC,                "Verify C");
		sTaskStrings.put(TaskNames.TERMINATION_BOOGIE,     "Analyze Termination Boogie");
		sTaskStrings.put(TaskNames.TERMINATION_C,          "Analyze Termination C");
		sTaskStrings.put(TaskNames.RANK_SYNTHESIS_BOOGIE,  "Synthesize ranking function Boogie");
		sTaskStrings.put(TaskNames.RANK_SYNTHESIS_C,       "Synthesize ranking function C");
		sTaskStrings.put(TaskNames.VerifyConcurrentBoogie, "Verify concurrent Boogie");
	}
	
	/**
	 * Initializes the workers mapping
	 */
	private static void initWorkers() {
		String description, name;

		System.out.println("Call of de.uni_freiburg.informatik.ultimate.website.Tasks.initWorkers() method");
		
		name = "Trace Abstraction";
		description = "An implementation of trace abstraction being able to verify programs.";
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

		name = "Lasso Ranker";
		description = "This is to synthesize ranking functions of lasso programs.";
		w = new Worker(name, "rank", description, null);
		// w.setInterfaceLayoutFontsize("40"); // sample for overwriting fontsize setting
		// w.setInterfaceLayoutOrientation("vertical"); // sample for overwriting orientation setting
		// w.setInterfaceLayoutTransitions("false"); // sample for overwriting animations setting
		// w.setContentURL("http://localhost:8080/Website/json/lasso_ranker.json"); // sample for setting an optional url
		sWorkers.put(w.getId(), w);

		name = "Automata Script";
		description = null;
		w = new Worker(name, "run", description, null);
		w.setUserInfo(""); // sample user information, being shown on Automata Script page
		sWorkers.put(w.getId(), w);
		
		attachToolchainsToWorker();
	}
	
	/**
	 * Adds toolchains automatically to worker array
	 * 
	 * @return 
	 */
	private static void attachToolchainsToWorker() {
		System.out.println("Call of de.uni_freiburg.informatik.ultimate.website.Tasks.attachToolchainsToWorker() method");
		for (Map.Entry<String, ArrayList<WebToolchain>> tcPair : getActiveToolchains().entrySet()) {
			/*
			tcPair.getKey();    // Taskname
			tcPair.getValue();	// ArrayList<WebToolchain>>
			*/
			for (WebToolchain toolchain : tcPair.getValue()) {
				if (!sWorkers.containsKey(Worker.toKey(toolchain.getName()))) {
					sWorkers.put(Worker.toKey(toolchain.getName()), new Worker(toolchain.getName(), null, null, null));
					System.out.println("Added " + toolchain.getName()  + " to Worker Array"); 
				}
				sWorkers.get(Worker.toKey(toolchain.getName())).addToolchain(toolchain);
			}
		}
	}

//	/**
//	 * Convert a task name enum object into its representing string.
//	 * 
//	 * @param name
//	 *            the enum element to convert
//	 * @return the string representive
//	 */
//	public static final String toString(TaskNames name) {
//		if (taskString.isEmpty()) {
//			initTaskNames();
//		}
//		if (!taskString.containsKey(name)) {
//			throw new IllegalArgumentException(
//					"This name is not contained in the list: " + name);
//		}
//		return taskString.get(name);
//	}

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
		System.out.println("Call of de.uni_freiburg.informatik.ultimate.website.Tasks.getWorker() method");
		if (sWorkers.isEmpty()) {
			initWorkers();
			System.out.println("Initialized workers, "+sWorkers.size()+" workers available:");
			for(Entry<String, Worker> worker : sWorkers.entrySet()){
				System.out.println(worker.getKey());
			}
		}

		// sort map by key
		/*Map<String, Worker> w = worker;
		List<String> keys = new ArrayList<String>(worker.keySet());
		Collections.sort(keys);
		
		for (String key : keys) { w.put(key, worker.get(key));}
		return w;*/
		
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
//			case AUTOMATA_SCRIPT:
//			return "ats";
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
	@SuppressWarnings("unchecked")
	public final static Map<String, ArrayList<WebToolchain>> getActiveToolchains() {
		System.out.println("Call of de.uni_freiburg.informatik.ultimate.website.Example.getActiveToolchains() method");
		if (sActiveToolchains.isEmpty()) {
			for (Class<WebToolchain> c : sActToolchains) {
				WebToolchain tc;
				try {
					tc = (WebToolchain) c.getConstructor().newInstance(
							(Object[]) null);
					for (TaskNames tn : tc.getTaskName()) {
						if (!sActiveToolchains.containsKey(tn.toString())) {
							sActiveToolchains.put(tn.toString(),
									new ArrayList<WebToolchain>());
							System.out.println("Added " + c.getCanonicalName()  + " to " +tn.toString()); 
						}
						sActiveToolchains.get(tn.toString()).add(tc);
					}
				} catch (Exception e) {
					System.out.println("Cannot add: " + c.toString());
					System.out.println(e.getCause());
				}
			}
		}
		return sActiveToolchains;
	}
}
