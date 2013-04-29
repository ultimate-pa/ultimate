/**
 * Describes the different task names.
 */
package de.uni_freiburg.informatik.ultimate.website;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.website.toolchains.AutomtaScriptTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieLassoRankerTC;
import de.uni_freiburg.informatik.ultimate.website.toolchains.BoogieTraceAbstractionTC;
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
	private static final Class[] actTCs = {AutomtaScriptTC.class, 
		BoogieTraceAbstractionTC.class,
		CTraceAbstractionTC.class, BoogieLassoRankerTC.class, CLassoRankerTC.class};
	/**
	 * The String representations of TaskNames.
	 */
	private static final Map<TaskNames, String> taskString = new HashMap<Tasks.TaskNames, String>();
	/**
	 * Active toolchains, listed by their task(s).
	 */
	private static final Map<String, ArrayList<Toolchain>> activeToolchains = new HashMap<String, ArrayList<Toolchain>>();

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
		
		/**
		 * Run automata test file.
		 */
		AUTOMATA_SCRIPT,
		/**
		 * Run automata test file.
		 */
		RunSmt2Script
		// If you add something here, add a String representation to
		// initTaskNames() as well!
	}

	/**
	 * Initializes the task name mapping.
	 */
	private static void initTaskNames() {
		// String should have at most 30 chars and must not be empty!
		taskString.put(TaskNames.AUTOMATA_SCRIPT, "Run Automata Script");
		taskString.put(TaskNames.RunSmt2Script, "Run Smt2Script (not yet available)");
		taskString.put(TaskNames.VerifyBoogie, "Verify Boogie");
		taskString.put(TaskNames.VerifyC, "Verify C");
		taskString.put(TaskNames.TERMINATION_BOOGIE, "Analyze Termination Boogie");
		taskString.put(TaskNames.TERMINATION_C, "Analyze Termination C");
	}

	/**
	 * Convert a task name enum object into its representing string.
	 * 
	 * @param name
	 *            the enum element to convert
	 * @return the string representive
	 */
	public static final String toString(TaskNames name) {
		if (taskString.isEmpty()) {
			initTaskNames();
		}
		if (!taskString.containsKey(name)) {
			throw new IllegalArgumentException(
					"This name is not contained in the list: " + name);
		}
		return taskString.get(name);
	}

	/**
	 * Getter for the string representation of task names.
	 * 
	 * @return a map of <code>TaskNames</code> to its String representation
	 */
	public static final Map<TaskNames, String> getTaskString() {
		if (taskString.isEmpty()) {
			initTaskNames();
		}
		return taskString;
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
				return "boogie";
			case VerifyC:
				return "c_cpp";
			case TERMINATION_BOOGIE:
				return "boogie";
			case TERMINATION_C:
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
	public final static Map<String, ArrayList<Toolchain>> getActiveToolchains() {
		if (activeToolchains.isEmpty()) {
			for (Class<Toolchain> c : actTCs) {
				Toolchain tc;
				try {
					tc = (Toolchain) c.getConstructor().newInstance(
							(Object[]) null);
					for (TaskNames tn : tc.getTaskName()) {
						if (!activeToolchains.containsKey(tn.toString())) {
							activeToolchains.put(tn.toString(),
									new ArrayList<Toolchain>());
							System.out.println("Added " + c.getCanonicalName()  + " to " +tn.toString()); 
						}
						activeToolchains.get(tn.toString()).add(tc);
					}
				} catch (Exception e) {
					System.out.println("Cannot add: " + c.toString());
					System.out.println(e.getCause());
				}
			}
		}
		return activeToolchains;
	}
}
