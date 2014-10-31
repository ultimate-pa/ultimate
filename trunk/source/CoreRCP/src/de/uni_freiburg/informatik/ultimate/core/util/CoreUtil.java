package de.uni_freiburg.informatik.ultimate.core.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import de.uni_freiburg.informatik.ultimate.result.IResult;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class CoreUtil {

	public interface IReduce<T, K> {
		public T reduce(K entry);
	}

	public interface IMapReduce<T, K> {
		public T reduce(T lastValue, K entry);
	}

	public interface IPredicate<T> {
		public boolean check(T entry);
	}

	private static String sPlatformLineSeparator = System.getProperty("line.separator");

	public static String getPlatformLineSeparator() {
		return sPlatformLineSeparator;
	}

	public static File writeFile(String filename, String content) throws IOException {
		File outputFile = new File(filename);
		outputFile.createNewFile();

		Writer out = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outputFile), "UTF-8"));
		try {
			out.write(content);
			return outputFile;
		} finally {
			out.close();
		}

	}

	public static void writeFile(String filename, String[] content) throws IOException {

		File outputFile = new File(filename);
		outputFile.createNewFile();

		Writer out = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outputFile), "UTF-8"));
		try {
			for (String s : content) {
				out.write(s);
				out.write(sPlatformLineSeparator);
			}

		} finally {
			out.close();
		}
	}

	public static String readFile(String filename) throws IOException {
		BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(new File(filename)), "UTF8"));
		try {

			StringBuilder sb = new StringBuilder();
			String line = br.readLine();
			while (line != null) {
				sb.append(line);
				sb.append(sPlatformLineSeparator);
				line = br.readLine();
			}
			return sb.toString();
		} finally {
			br.close();
		}
	}

	public static String readFile(File file) throws IOException {
		return readFile(file.getAbsolutePath());
	}

	/**
	 * Returns all elements of a collection that match the check defined by
	 * predicate.
	 * 
	 * @param collection
	 *            The collection you want to filter. May not be null.
	 * @param predicate
	 *            The predicate you want to use to filter said collection. May
	 *            not be null.
	 * @return A new collection that only contains elements for which
	 *         {@link IPredicate#check(Object)} returned true.
	 */
	public static <E> Collection<E> where(Collection<E> collection, IPredicate<E> predicate) {
		ArrayList<E> rtr = new ArrayList<>();
		for (E entry : collection) {
			if (predicate.check(entry)) {
				rtr.add(entry);
			}
		}
		return rtr;
	}

	/**
	 * Returns a {@link Set} of elements that are created by applying the
	 * reducer to every element in the collection.
	 * 
	 * @param collection
	 *            May not be null.
	 * @param reducer
	 *            May not be null.
	 * @return
	 */
	public static <T, E> Set<T> selectDistinct(Collection<E> collection, IReduce<T, E> reducer) {
		Set<T> rtr = new HashSet<>();
		for (E entry : collection) {
			rtr.add(reducer.reduce(entry));
		}
		return rtr;
	}

	public static <T, E> Collection<T> select(Collection<E> collection, IReduce<T, E> reducer) {
		Collection<T> rtr = new ArrayList<>();
		for (E entry : collection) {
			rtr.add(reducer.reduce(entry));
		}
		return rtr;
	}

	public static <E> Collection<E> flattenMapValuesToCollection(Map<?, E> map) {
		Collection<E> rtr = new ArrayList<>();
		for (Entry<?, E> entry : map.entrySet()) {
			rtr.add(entry.getValue());
		}
		return rtr;
	}

	public static <T, E> T reduce(Set<E> collection, IMapReduce<T, E> reducer) {
		T lastValue = null;
		for (E entry : collection) {
			lastValue = reducer.reduce(lastValue, entry);
		}
		return lastValue;
	}

	public static <T, E> T reduce(Collection<E> collection, IMapReduce<T, E> reducer) {
		T lastValue = null;
		for (E entry : collection) {
			lastValue = reducer.reduce(lastValue, entry);
		}
		return lastValue;
	}

	/**
	 * Indents a (possibly multiline) String such that the resulting
	 * StringBuilder object contains the same String, but indented with the
	 * indentPrefix. It also converts line breaks to the system-specific line
	 * separator.
	 * 
	 * @param original
	 * @param indentPrefix
	 * @param forceRemoveLastLinebreak
	 *            When true, the last linebreak will always be removed, when
	 *            false, an existing last line break will be preserved (but
	 *            converted to system-specific line break)
	 * @return
	 */
	public static StringBuilder indentMultilineString(String original, String indentPrefix,
			boolean forceRemoveLastLinebreak) {
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		String[] splitted = original.split("\\r?\\n");

		for (String s : splitted) {
			sb.append(indentPrefix).append(s).append(lineSeparator);
		}

		char last = original.charAt(original.length() - 1);
		if (forceRemoveLastLinebreak || (last != '\n' && last != '\r')) {
			sb.replace(sb.length() - lineSeparator.length(), sb.length(), "");
		}
		return sb;
	}

	public static String getCurrentDateTimeAsString() {
		return new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss-SSS").format(Calendar.getInstance().getTime());
	}

	/**
	 * Flattens a string, i.e. removes all line breaks and replaces them with
	 * separator
	 * 
	 * @param original
	 * @param separator
	 * @return
	 */
	public static StringBuilder flatten(String original, String separator) {
		StringBuilder sb = new StringBuilder();
		String[] splitted = original.split("\\r?\\n");
		for (String s : splitted) {
			sb.append(s).append(separator);
		}
		sb.replace(sb.length() - separator.length(), sb.length(), "");
		return sb;
	}

	public static <E> Collection<E> firstN(Collection<E> collection, int n) {
		ArrayList<E> rtr = new ArrayList<E>(n);
		int i = 1;
		for (E elem : collection) {
			rtr.add(elem);
			++i;
			if (n < i) {
				break;
			}
		}
		return rtr;
	}

	/**
	 * Returns new Collections that contains all IResults from ultimateIResults
	 * that are subclasses of the class resClass.
	 */
	public static <E extends IResult> Collection<E> filterResults(Map<String, List<IResult>> ultimateIResults,
			Class<E> resClass) {
		ArrayList<E> filteredList = new ArrayList<E>();
		for (Entry<String, List<IResult>> entry : ultimateIResults.entrySet()) {
			for (IResult res : entry.getValue()) {
				if (res.getClass().isAssignableFrom(resClass)) {
					@SuppressWarnings("unchecked")
					E benchmarkResult = (E) res;
					filteredList.add((E) benchmarkResult);
				}
			}
		}
		return filteredList;
	}

}
