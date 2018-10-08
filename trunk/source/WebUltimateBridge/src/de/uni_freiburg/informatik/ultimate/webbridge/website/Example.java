/**
 * Holds example files.
 */
package de.uni_freiburg.informatik.ultimate.webbridge.website;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.FileLocator;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 14.02.2012
 */
public final class Example {
	private static final String EXAMPLE_DIR_PREFIX =
			"/de/uni_freiburg/informatik/ultimate/webbridge/resources/examples/";
	/**
	 * The files content.
	 */
	private String mFileContent;
	/**
	 * The files name; a String describing the file - this is the name shown to the web user in a dropdown box.
	 */
	private final String mFileName;
	/**
	 * The path to the file - actually the files real name without an absolute path! This is used by the Class Loader to
	 * find the file!
	 */
	private String mFilePath;
	/**
	 * The examples identifier used to uniquely identify the example on communication between client and server.
	 */
	private final String mId;
	/**
	 * The taskNames for which these example is applicable.
	 */
	private Tasks.TaskNames[] mTaskNames;
	/**
	 * The map of examples - generated automatically and holding the representations of the examples, sorted by the
	 * corresponding task(s). This implies, that examples with multiple tasks are contained multiply!
	 */
	private static final Map<Tasks.TaskNames, ArrayList<Example>> sExamplesByTask = new HashMap<>();
	/**
	 * Set of IDs - used to verify, that the ids are really unique!
	 */
	private static final Set<String> sIds = new HashSet<>();
	/**
	 * List of examples, sorted by their ids - each example is therefore contained only once!
	 */
	private static final Map<String, Example> EXAMPLES_BY_ID = new HashMap<>();

	/**
	 * Initialize the Example lists.
	 */
	private static void init() {
		SimpleLogger.log("Initializing Examples.");
		final ArrayList<Example> list = new ArrayList<>();

		final Tasks.TaskNames[] verifyC = { Tasks.TaskNames.AUTOMIZER_C, TaskNames.KOJAK_C, TaskNames.TAIPAN_C };
		addAllFilesInExamplesSubfolder(list, "verifyC/", verifyC);

		final Tasks.TaskNames[] verifyBoogie =
				{ Tasks.TaskNames.AUTOMIZER_BOOGIE, Tasks.TaskNames.KOJAK_BOOGIE, TaskNames.TAIPAN_BOOGIE };
		addAllFilesInExamplesSubfolder(list, "verifyBoogie/", verifyBoogie);

		final Tasks.TaskNames[] rankBoogie = { Tasks.TaskNames.RANK_SYNTHESIS_BOOGIE };
		addAllFilesInExamplesSubfolder(list, "rankBoogie/", rankBoogie);

		final Tasks.TaskNames[] rankC = { Tasks.TaskNames.RANK_SYNTHESIS_C };
		addAllFilesInExamplesSubfolder(list, "rankC/", rankC);

		final Tasks.TaskNames[] terminatonC = { Tasks.TaskNames.TERMINATION_C };
		addAllFilesInExamplesSubfolder(list, "terminationC/", terminatonC);

		final Tasks.TaskNames[] terminationBoogie = { Tasks.TaskNames.TERMINATION_BOOGIE };
		addAllFilesInExamplesSubfolder(list, "terminationBoogie/", terminationBoogie);

		final Tasks.TaskNames[] automataScript = { Tasks.TaskNames.AUTOMATA_SCRIPT };
		addAllFilesInExamplesSubfolder(list, "AUTOMATA_SCRIPT/", automataScript);

		final Tasks.TaskNames[] verifyConcurrentBoogie = { Tasks.TaskNames.CONCURRENT_BOOGIE };
		addAllFilesInExamplesSubfolder(list, "verifyConcurrentBoogie/", verifyConcurrentBoogie);

		final Tasks.TaskNames[] ltlAutomizer = { Tasks.TaskNames.LTLAUTOMIZER_C };
		addAllFilesInExamplesSubfolder(list, "ltlautomizer/", ltlAutomizer);

		// load the content for the examples in the list and place it in the
		// sExamplesByTask map (via the alternate example constructor)
		for (final Example e : list) {
			try {
				new Example(e.mFileName, e.mId, e.mTaskNames, readFile(e.mFilePath));
			} catch (final IOException ex) {
				/* file cannot be parsed -> skip it! */
				ex.printStackTrace();
			} catch (final IllegalArgumentException ex) {
				ex.printStackTrace();
				/* file not valid -> skip it! */
			}
		}
	}

	/**
	 * Returns a map of example files sorted by their corresponding task. This map
	 *
	 * @return a map of example files.
	 */
	public static Map<Tasks.TaskNames, ArrayList<Example>> getExamples() {
		if (sExamplesByTask.isEmpty()) {
			SimpleLogger.log("sortedMap is empty");
			init();
		}
		return sExamplesByTask;
	}

	/**
	 * Constructor.
	 *
	 * @param name
	 *            the file name to be shown in the Website
	 * @param taskNames
	 *            the corresponding tasks, where this example can be used
	 * @param content
	 *            the file content
	 * @param id
	 *            the id
	 */
	private Example(final String name, final String id, final Tasks.TaskNames[] taskNames, final String content) {
		if (name == null || name.equals("") || name.length() > 30) {
			throw new IllegalArgumentException("Not a valid file name!");
		}
		if (content == null || content.equals("")) {
			throw new IllegalArgumentException("File content empty!");
		}
		if (taskNames.length == 0) {
			throw new IllegalArgumentException("Example must be assign to at least one TaskName!");
		}
		if (sIds.contains(id)) {
			throw new IllegalArgumentException("ID must be unique! " + "Not unique: " + name + " " + id);
		}
		if (id == null || id.equals("")) {
			throw new IllegalArgumentException("ID cannot be empty!");
		}
		if (id.length() > 30) {
			throw new IllegalArgumentException("ID cannot be longer than 30 characters!");
		}
		if (!id.matches("[a-zA-Z0-9]*")) {
			throw new IllegalArgumentException("ID must be element of (a-Z0-9)*");
		}
		mFileName = name;
		mFileContent = content;
		mId = id;
		sIds.add(id);
		for (final Tasks.TaskNames tn : taskNames) {
			if (!sExamplesByTask.containsKey(tn)) {
				sExamplesByTask.put(tn, new ArrayList<Example>());
			}
			sExamplesByTask.get(tn).add(this);
		}
		EXAMPLES_BY_ID.put(id, this);
	}

	/**
	 * Constructor.
	 *
	 * @param name
	 *            the file name to be shown in the Website
	 * @param path
	 *            the path to the file
	 * @param taskNames
	 *            the corresponding tasks, where this example can be used
	 * @param id
	 *            the id
	 */
	private Example(final String name, final String id, final String path, final Tasks.TaskNames[] taskNames) {
		mFileName = name;
		mFilePath = path;
		mTaskNames = taskNames;
		mId = id;
	}

	/**
	 * Reads a file and returns its content in a String
	 *
	 * @param name
	 *            the path to the file
	 * @return the file content in a String
	 * @throws IOException
	 *             care for it ...
	 */
	private static final String readFile(final String name) throws IOException {
		final String example = EXAMPLE_DIR_PREFIX + name;
		final InputStream inStream = Example.class.getResourceAsStream(example);
		if (inStream == null) {
			return "// File not found!";
		}

		final BufferedReader in = new BufferedReader(new InputStreamReader(inStream));
		String inputLine;
		final String eol = System.getProperty("line.separator");
		final StringBuilder fileContents = new StringBuilder();
		try {
			while ((inputLine = in.readLine()) != null) {
				fileContents.append(inputLine + eol);
			}
			return fileContents.toString();
		} finally {
			in.close();
		}
	}

	/**
	 * Return the filenames of the files in the folder /resources/examples/ + dirSuffix (path given relative to root of
	 * this package).
	 *
	 * We use the classloader to get the URL of this folder. We support only URLs with protocol <i>file</i> and
	 * <i>bundleresource</i>. At the moment these are the only ones that occur in Website and WebsiteEclipseBridge.
	 */
	static private String[] filenamesOfFilesInSubdirectory(final String dirSuffix) {
		final String dir = EXAMPLE_DIR_PREFIX + dirSuffix;
		SimpleLogger.log("Trying to get all files in directory " + dir);
		final URL dirURL = Example.class.getClassLoader().getResource(dir);
		if (dirURL == null) {
			SimpleLogger.log("Folder " + dir + " does not exist");
			return new String[0];
		}
		SimpleLogger.log("URL " + dirURL);
		final String protocol = dirURL.getProtocol();
		File dirFile = null;
		if (protocol.equals("file")) {
			try {
				dirFile = new File(dirURL.toURI());
			} catch (final URISyntaxException e) {
				e.printStackTrace();
				SimpleLogger.log("Failed");
				return new String[0];
			}
		} else if (protocol.equals("bundleresource")) {
			try {
				final URL fileURL = FileLocator.toFileURL(dirURL);
				dirFile = new File(fileURL.toURI());
			} catch (final Exception e) {
				e.printStackTrace();
				SimpleLogger.log("Failed");
				return new String[0];
			}
		} else {
			SimpleLogger.log("Unkown protocol " + protocol);
			return new String[0];
		}
		final String[] content = dirFile.list();
		if (content == null) {
			SimpleLogger.log("No folder:" + dirURL);
			return new String[0];
		}
		Arrays.sort(content);
		return content;
	}

	/**
	 * Add all files in subfolder of /resource/example as Example to list for taskNames. The id of the examples is
	 * defined by hash codes.
	 */
	static private void addAllFilesInExamplesSubfolder(final List<Example> list, final String subfolder,
			final TaskNames[] taskNames) {
		final String[] filesInSubfolder = filenamesOfFilesInSubdirectory(subfolder);
		for (final String filename : filesInSubfolder) {
			final String exPath = subfolder + filename;
			final String id = String.valueOf(Math.abs(exPath.hashCode()));
			// crop name to 30 characters
			String name;
			if (filename.length() > 30) {
				name = filename.substring(0, Math.min(27, filename.length())).concat("...");
			} else {
				name = filename;
			}
			list.add(new Example(name, id, exPath, taskNames));
			System.out.println("Added example " + filename + " and assigned id " + id);
		}
	}

	/**
	 * Getter for file content.
	 *
	 * @return the fileContent
	 */
	public String getFileContent() {
		return mFileContent;
	}

	/**
	 * Getter for file name.
	 *
	 * @return the fileName
	 */
	public String getFileName() {
		return mFileName;
	}

	/**
	 * Getter for task name.
	 *
	 * @return the taskNames
	 */
	public Tasks.TaskNames[] getTaskNames() {
		return mTaskNames;
	}

	/**
	 * Getter for the examples id.
	 *
	 * @return the id
	 */
	public String getId() {
		return mId;
	}

	public String getInfoString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Example ").append(getId()).append(" from File ").append(getFileName()).append(" (Tasks [");

		if (getTaskNames() != null) {
			for (final TaskNames taskName : getTaskNames()) {
				sb.append(taskName).append(", ");
			}
			if (getTaskNames().length > 0) {
				// sb.delete(sb.length() - 2, sb.length());
			}
		}
		sb.append("])");
		return sb.toString();
	}

	/**
	 * Get the example with the identifier id.
	 *
	 * @param id
	 *            the identifier
	 * @return the corresponding example or null, if ID not found!
	 */
	public static final Example get(final String id) {
		if (EXAMPLES_BY_ID.isEmpty()) {
			SimpleLogger.log("Example list is empty, initializing...");
			init();
		}
		final Example ex = EXAMPLES_BY_ID.get(id);
		if (ex != null) {
			SimpleLogger.log("Get example returns " + ex.getInfoString());
		} else {
			SimpleLogger.log("Get example returns NULL because ID " + id + " was not found");
		}

		return ex;
	}
}
