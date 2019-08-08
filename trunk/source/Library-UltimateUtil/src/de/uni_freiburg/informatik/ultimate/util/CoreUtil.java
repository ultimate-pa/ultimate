/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Comparator;
import java.util.Date;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Scanner;
import java.util.Set;
import java.util.TimeZone;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
import java.util.function.Predicate;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class CoreUtil {

	private static final String PLATFORM_LINE_SEPARATOR = System.getProperty("line.separator");
	public static final String OS = System.getProperty("os.name");
	public static final boolean OS_IS_WINDOWS = OS.toLowerCase().indexOf("win") >= 0;

	public static String getPlatformLineSeparator() {
		return PLATFORM_LINE_SEPARATOR;
	}

	public static String getIsoUtcTimestamp() {
		final TimeZone tz = TimeZone.getTimeZone("UTC");
		// Quoted "Z" to indicate UTC, no timezone offset
		final DateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm'Z'");
		df.setTimeZone(tz);
		return df.format(new Date());
	}

	/**
	 * Converts Strings in upper case, e.g. THIS_IS_A_NAME, to CamelCase, e.g., ThisIsAName. If the string already
	 * contains some lower-case characters, no conversion is performed.
	 *
	 * @param value
	 *            The string that should be converted.
	 * @return The name in Camel Case.
	 */
	public static String getUpperToCamelCase(final String value) {
		if (value == null) {
			return value;
		}
		if (!value.toUpperCase().equals(value)) {
			// string has lower-case, ignore
			return value;
		}
		final StringBuilder sb = new StringBuilder();
		for (final String s : value.split("_")) {
			sb.append(Character.toUpperCase(s.charAt(0)));
			if (s.length() > 1) {
				sb.append(s.substring(1).toLowerCase());
			}
		}
		return sb.toString();
	}

	/**
	 * @param cl
	 *            A classloader that has access to version.properties (i.e., the one the core uses)
	 * @return a string describing the state of the current git repository or null iff version.properties does not
	 *         exist.
	 */
	public static String readGitVersion(final ClassLoader cl) {
		final Properties properties = new Properties();
		try {
			final InputStream prop = cl.getResourceAsStream("version.properties");
			if (prop == null) {
				return "?-m";
			}
			properties.load(prop);
		} catch (final IOException e) {
			return null;
		}

		final String hash = properties.getProperty("git.commit.id.abbrev", "UNKNOWN");
		final String dirty = properties.getProperty("git.dirty", "UNKNOWN");

		return hash + ("UNKNOWN".equals(dirty) ? "" : "true".equals(dirty) ? "-m" : "");
	}

	/**
	 * Traverses the OS' PATH and searches for a file that fulfills the following conditions.
	 * <ul>
	 * <li>The filename starts with {@code <name>},
	 * <li>the current process is allowed to execute it,
	 * <li>it looks like some known executable binary (i.e., has the right magic numbers in the beginning).
	 * </ul>
	 */
	public static File findExecutableBinaryOnPath(final String name) {
		final Predicate<File> funLooksLikeExectuable;
		if (CoreUtil.OS_IS_WINDOWS) {
			// Windows uses the Portable Executable format starting with 0x4d5a (ASCII characters MZ)
			final byte[] exeMagicNumber = {'M', 'Z'};
			funLooksLikeExectuable = f -> hasMagicNumber(f, exeMagicNumber);
		} else {
			// Just assume Linux: ELF format executables start with 0x7f454c46 (ASCII characters <DEL>ELF)
			final byte[] elfMagicNumber = {0x7f, 'E', 'L', 'F'};
			funLooksLikeExectuable = f -> hasMagicNumber(f, elfMagicNumber);
		}

		for (final String dirname : System.getenv("PATH").split(File.pathSeparator)) {
			final File[] files = new File(dirname).listFiles(f -> f.getName().startsWith(name));
			if (files == null) {
				continue;
			}
			for (final File file : files) {
				if (file.isFile() && file.canExecute() && funLooksLikeExectuable.test(file)) {
					return file;
				}
			}
		}
		return null;
	}

	private static boolean hasMagicNumber(final File file, final byte[] magicNumber) {
		try (final FileInputStream input = new FileInputStream(file)) {
			final byte[] firstBytes = new byte[magicNumber.length];
			input.read(firstBytes);
			return Arrays.equals(firstBytes, magicNumber);
		} catch (final Exception e) {
			return false;
		}
	}

	public static File writeFile(final File file, final String content) throws IOException {
		writeFile(fw -> fw.append(content), false, file);
		return file;
	}

	public static File writeFile(final String filename, final String content) throws IOException {
		return writeFile(filename, content, false);
	}

	public static File writeFile(final String filename, final String[] content) throws IOException {
		return writeFile(filename, content, false);
	}

	public static File appendFile(final String filename, final String content) throws IOException {
		return writeFile(filename, content, true);
	}

	public static File appendFile(final String filename, final String[] content) throws IOException {
		return writeFile(filename, content, true);
	}

	private static File writeFile(final String filename, final String[] content, final boolean append)
			throws IOException {
		if (content == null || content.length == 0) {
			return null;
		}
		final File file = createFile(filename);
		final IWriterConsumer funWrite = fw -> {
			for (final String line : content) {
				fw.append(line);
				fw.append(PLATFORM_LINE_SEPARATOR);
			}
		};
		writeFile(funWrite, append, file);
		return file;
	}

	private static File writeFile(final String filename, final String content, final boolean append)
			throws IOException {
		if (content == null || content.isEmpty()) {
			return null;
		}
		final File file = createFile(filename);
		writeFile(fw -> fw.append(content), append, file);
		return file;
	}

	private static void writeFile(final IWriterConsumer funWrite, final boolean append, final File file)
			throws IOException {
		try (FileOutputStream os = new FileOutputStream(file, append);
				Writer fw = new BufferedWriter(new OutputStreamWriter(os, "UTF-8"))) {
			funWrite.consume(fw);
			fw.close();
		}
	}

	private static File createFile(final String filename) {
		final File file = new File(filename);
		if (!file.isDirectory()) {
			final File parentFile = file.getParentFile();
			if (parentFile != null) {
				parentFile.mkdirs();
			}
		}
		return file;
	}

	public static List<String> readFileLineByLine(final String filename) throws IOException {
		final BufferedReader br =
				new BufferedReader(new InputStreamReader(new FileInputStream(new File(filename)), "UTF8"));
		final List<String> rtr = new ArrayList<>();
		try {
			String line = br.readLine();
			while (line != null) {
				rtr.add(line);
				line = br.readLine();
			}
			return rtr;
		} finally {
			br.close();
		}
	}

	/**
	 * Convert the given String to a path and read from the file there line by line, calling the supplied consumer for
	 * each line.
	 *
	 * @throws IOException
	 */
	public static void readFileLineByLine(final String filename, final Consumer<String> consumer) throws IOException {
		final BufferedReader br =
				new BufferedReader(new InputStreamReader(new FileInputStream(new File(filename)), "UTF8"));
		try {
			String line = br.readLine();
			while (line != null) {
				consumer.accept(line);
				line = br.readLine();
			}
		} finally {
			br.close();
		}
	}

	public static String readFile(final String filename) throws IOException {
		final StringBuilder sb = new StringBuilder();
		readFileLineByLine(filename).stream().forEach(line -> sb.append(line).append(PLATFORM_LINE_SEPARATOR));
		return sb.toString();
	}

	public static String readFile(final File file) throws IOException {
		return readFile(file.getAbsolutePath());
	}

	public static List<String> readFileLineByLine(final File file) throws IOException {
		return readFileLineByLine(file.getAbsolutePath());
	}

	/**
	 * Get the extension of a file, i.e., the part of the filename after the last '.'. If there is no extension, return
	 * an empty string.
	 *
	 * @param file
	 *            The file for which the extension should be obtained.
	 * @return The extension.
	 */
	public static String getFileExtension(final File file) {
		assert file != null;
		assert file.isFile();
		assert !file.isDirectory();
		final String filename = file.getName();

		final int i = filename.lastIndexOf('.');
		if (i > 0) {
			return filename.substring(i + 1);
		}
		return "";
	}

	/**
	 * Returns all elements of a collection that match the check defined by predicate.
	 *
	 * @param collection
	 *            The collection you want to filter. May not be null.
	 * @param predicate
	 *            The predicate you want to use to filter said collection. May not be null.
	 * @return A new collection that only contains elements for which {@link IPredicate#check(Object)} returned true.
	 */
	public static <E> Collection<E> where(final Collection<E> collection, final Predicate<E> predicate) {
		final ArrayList<E> rtr = new ArrayList<>();
		for (final E entry : collection) {
			if (predicate.test(entry)) {
				rtr.add(entry);
			}
		}
		return rtr;
	}

	/**
	 * Returns a {@link Set} of elements that are created by applying the reducer to every element in the collection.
	 *
	 * @param collection
	 *            May not be null.
	 * @param reducer
	 *            May not be null.
	 * @return
	 */
	public static <T, E> Set<T> selectDistinct(final Collection<E> collection, final IReduce<T, E> reducer) {
		final Set<T> rtr = new HashSet<>();
		for (final E entry : collection) {
			rtr.add(reducer.reduce(entry));
		}
		return rtr;
	}

	public static <T, E> Collection<T> select(final Collection<E> collection, final IReduce<T, E> reducer) {
		final Collection<T> rtr = new ArrayList<>();
		for (final E entry : collection) {
			rtr.add(reducer.reduce(entry));
		}
		return rtr;
	}

	public static <E> Collection<E> flattenMapValuesToCollection(final Map<?, E> map) {
		final Collection<E> rtr = new ArrayList<>();
		for (final Entry<?, E> entry : map.entrySet()) {
			rtr.add(entry.getValue());
		}
		return rtr;
	}

	public static <T, E> T reduce(final Set<E> collection, final IMapReduce<T, E> reducer) {
		T lastValue = null;
		for (final E entry : collection) {
			lastValue = reducer.reduce(lastValue, entry);
		}
		return lastValue;
	}

	public static <T, E> T reduce(final Collection<E> collection, final IMapReduce<T, E> reducer) {
		T lastValue = null;
		for (final E entry : collection) {
			lastValue = reducer.reduce(lastValue, entry);
		}
		return lastValue;
	}

	/**
	 * Indents a (possibly multiline) String such that the resulting StringBuilder object contains the same String, but
	 * indented with the indentPrefix. It also converts line breaks to the system-specific line separator.
	 *
	 * @param original
	 * @param indentPrefix
	 * @param forceRemoveLastLinebreak
	 *            When true, the last linebreak will always be removed, when false, an existing last line break will be
	 *            preserved (but converted to system-specific line break)
	 * @return
	 */
	public static StringBuilder indentMultilineString(final String original, final String indentPrefix,
			final boolean forceRemoveLastLinebreak) {
		final StringBuilder sb = new StringBuilder();
		final String lineSeparator = System.getProperty("line.separator");
		final String[] splitted = original.split("\\r?\\n");

		for (final String s : splitted) {
			sb.append(indentPrefix).append(s).append(lineSeparator);
		}

		final char last = original.charAt(original.length() - 1);
		if (forceRemoveLastLinebreak || (last != '\n' && last != '\r')) {
			sb.replace(sb.length() - lineSeparator.length(), sb.length(), "");
		}
		return sb;
	}

	public static String getCurrentDateTimeAsString() {
		return new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss-SSS").format(Calendar.getInstance().getTime());
	}

	/**
	 * Flattens a string, i.e. removes all line breaks and replaces them with separator
	 */
	public static StringBuilder flatten(final String original, final String separator) {
		final StringBuilder sb = new StringBuilder();
		final String[] splitted = original.split("\\r?\\n");
		for (final String s : splitted) {
			sb.append(s).append(separator);
		}
		sb.replace(sb.length() - separator.length(), sb.length(), "");
		return sb;
	}

	/**
	 * Replace all files that represent directories by their contents (recursively).
	 */
	public static List<File> flattenDirectories(final Collection<File> files) {
		final Deque<File> worklist = new ArrayDeque<>();
		final List<File> rtr = new ArrayList<>();
		worklist.addAll(files);
		while (!worklist.isEmpty()) {
			final File file = worklist.removeFirst();
			if (file.isFile()) {
				rtr.add(file);
				continue;
			}
			worklist.addAll(Arrays.asList(file.listFiles()));
		}
		return rtr;
	}

	public static <E> Collection<E> firstN(final Collection<E> collection, final int n) {
		final ArrayList<E> rtr = new ArrayList<>(n);
		int i = 1;
		for (final E elem : collection) {
			rtr.add(elem);
			++i;
			if (n < i) {
				break;
			}
		}
		return rtr;
	}

	/**
	 * Create a copy of one or more arrays. If there are more than one array, concatenate all of them.
	 */
	@SafeVarargs
	public static <T> T[] concatAll(final T[] first, final T[]... rest) {
		int totalLength = first.length;
		for (final T[] array : rest) {
			totalLength += array.length;
		}
		final T[] result = Arrays.copyOf(first, totalLength);
		int offset = first.length;
		for (final T[] array : rest) {
			System.arraycopy(array, 0, result, offset, array.length);
			offset += array.length;
		}
		return result;
	}

	public static String convertStreamToString(final InputStream is) {
		@SuppressWarnings("resource")
		final Scanner s = new Scanner(is).useDelimiter("\\A");
		return s.hasNext() ? s.next() : "";
	}

	/**
	 * Determines if an {@link Iterable} is sorted according to the natural comparator. The order of objects that are
	 * equal according to the natural ordering is irrelevant.
	 *
	 * @param iterable
	 *            The {@link Iterable} that should be checked.
	 * @return true if the {@link Iterable} is sorted, false otherwise.
	 */
	public static <T extends Comparable<? super T>> boolean isSorted(final Iterable<T> iterable) {
		final Iterator<T> iter = iterable.iterator();
		if (!iter.hasNext()) {
			// empty iterables are always sorted
			return true;
		}
		T last = iter.next();
		while (iter.hasNext()) {
			final T current = iter.next();
			final int cmp = last.compareTo(current);
			if (cmp > 0) {
				return false;
			}
			last = current;
		}
		return true;
	}

	/**
	 * Determines if an {@link Iterable} is sorted according to the provided {@link Comparator}omparator. The order of
	 * objects that are equal according to the comparator is irrelevant.
	 *
	 * @param iterable
	 *            The {@link Iterable} that should be checked.
	 * @param comparator
	 *            The comparator that should be used for the sorting check.
	 * @return true if the {@link Iterable} is sorted, false otherwise.
	 */
	public static <T extends Comparable<? super T>> boolean isSorted(final Iterable<T> iterable,
			final Comparator<T> comparator) {
		final Iterator<T> iter = iterable.iterator();
		if (!iter.hasNext()) {
			// empty iterables are always sorted
			return true;
		}
		T last = iter.next();
		while (iter.hasNext()) {
			final T current = iter.next();
			if (comparator.compare(last, current) >= 0) {
				return false;
			}
			last = current;
		}
		return true;
	}

	/**
	 * @return a new {@link Map} that contains all key-value pairs of map whose key is contained in filter.
	 */
	public static <K, V> Map<K, V> constructFilteredMap(final Map<K, V> map, final Collection<K> filter) {
		final HashMap<K, V> result = new HashMap<>();
		for (final K key : filter) {
			final V value = map.get(key);
			if (value != null) {
				result.put(key, value);
			}
		}
		return result;
	}

	/**
	 * Construct a new {@link Set} that contains the elements of a given Iterable.
	 */
	public static <E> Set<E> constructHashSet(final Iterable<E> iterable) {
		final HashSet<E> result = new HashSet<>();
		for (final E element : iterable) {
			result.add(element);
		}
		return result;
	}

	/**
	 * Converts a number of bytes to a human readable String containing the byte number as the highest compatible unit.
	 *
	 * @param bytes
	 *            A number of bytes
	 * @param si
	 *            true iff SI units should be used (base 1000, without the "i")
	 * @return
	 */
	public static String humanReadableByteCount(final long bytes, final boolean si) {
		final int unit = si ? 1000 : 1024;
		if (bytes < unit) {
			return bytes + " B";
		}
		final int exp = (int) (Math.log(bytes) / Math.log(unit));
		final String pre = (si ? "kMGTPE" : "KMGTPE").charAt(exp - 1) + (si ? "" : "i");
		return String.format("%.1f %sB", bytes / Math.pow(unit, exp), pre);
	}

	public static String humanReadableNumber(final long number) {
		final int unit = 1000;
		if (number < unit) {
			return Long.toString(number);
		}
		final int exp = (int) (Math.log(number) / Math.log(unit));
		final String pre = String.valueOf("KMGTPE".charAt(exp - 1));
		return String.format("%.1f %s", number / Math.pow(unit, exp), pre);
	}

	/***
	 * Returns a String representation of a collection by calling toString on each object in the collection.
	 *
	 * @param collection
	 * @param delimiter
	 * @return
	 */
	public static String join(final Collection<?> collection, final String delimiter) {
		final StringBuilder builder = new StringBuilder();
		final Iterator<?> iter = collection.iterator();
		while (iter.hasNext()) {
			builder.append(iter.next());
			if (!iter.hasNext()) {
				break;
			}
			builder.append(delimiter);
		}
		return builder.toString();
	}

	public static <T> String join(final T[] collection, final String delimiter) {
		final StringBuilder builder = new StringBuilder();
		for (final T elem : collection) {
			builder.append(elem);
			builder.append(delimiter);
		}
		return builder.toString();
	}

	/**
	 * Returns a String representation of time as a fraction of the largest whole unit.
	 *
	 * I.e. 1001ms becomes 1,001s, 25h become 1,041d.
	 *
	 * @param time
	 *            The amount of time
	 * @param unit
	 *            The unit of the amount.
	 * @param decimal
	 *            The decimal accurracy of the ouptut.
	 * @return A String with unit symbol.
	 */
	public static String humanReadableTime(final long time, final TimeUnit unit, final int decimal) {
		return humanReadableTime((double) time, unit, decimal);
	}

	/**
	 * Returns a String representation of time as a fraction of the largest whole unit.
	 *
	 * I.e. 1001ms becomes 1,001s, 25h become 1,041d.
	 *
	 * @param time
	 *            The amount of time
	 * @param unit
	 *            The unit of the amount.
	 * @param decimal
	 *            The decimal accurracy of the ouptut.
	 * @return A String with unit symbol.
	 */
	public static String humanReadableTime(final double time, final TimeUnit unit, final int decimal) {
		final String[] units = { "ns", "µs", "ms", "s", "m", "h", "d" };

		switch (unit) {
		case DAYS:
			return String.format("%." + decimal + "f %s", time, units[6]);
		case HOURS:
			if (time > 24) {
				return humanReadableTime(time / 24.0, TimeUnit.DAYS, decimal);
			}
			return String.format("%." + decimal + "f %s", time, units[5]);
		case MINUTES:
			if (time > 60) {
				return humanReadableTime(time / 60.0, TimeUnit.HOURS, decimal);
			}
			return String.format("%." + decimal + "f %s", time, units[4]);
		case SECONDS:
			if (time > 60) {
				return humanReadableTime(time / 60.0, TimeUnit.MINUTES, decimal);
			}
			return String.format("%." + decimal + "f %s", time, units[3]);
		case MILLISECONDS:
			if (time > 1000) {
				return humanReadableTime(time / 1000.0, TimeUnit.SECONDS, decimal);
			}
			return String.format("%." + decimal + "f %s", time, units[2]);
		case MICROSECONDS:
			if (time > 1000) {
				return humanReadableTime(time / 1000.0, TimeUnit.MILLISECONDS, decimal);
			}
			return String.format("%." + decimal + "f %s", time, units[1]);
		case NANOSECONDS:
			if (time > 1000) {
				return humanReadableTime(time / 1000.0, TimeUnit.MICROSECONDS, decimal);
			}
			return String.format("%." + decimal + "f %s", time, units[0]);
		default:
			throw new UnsupportedOperationException(unit + " TimeUnit not yet implemented");
		}
	}

	/**
	 * Filter Collection to all elements that are subclasses of clazz.
	 */
	@SuppressWarnings("unchecked")
	public static <E> Collection<E> filter(final Collection<?> iterable, final Class<E> clazz) {
		final ArrayList<E> filteredList = new ArrayList<>();
		for (final Object e : iterable) {
			if (clazz.isAssignableFrom(e.getClass())) {
				filteredList.add((E) e);
			}
		}
		return filteredList;
	}

	/**
	 * Recursively delete the specified folder and all of its contents.
	 */
	public static void deleteDirectory(final File folder) {
		deleteDirectoryContents(folder);
		if (!folder.delete()) {
			folder.deleteOnExit();
		}
	}

	/**
	 * Recursively delete the contents of the specified folder.
	 */
	public static void deleteDirectoryContents(final File folder) {
		final File[] files = folder.listFiles();
		if (files != null) {
			// some JVMs return null for empty dirs
			for (final File f : files) {
				if (f.isDirectory()) {
					deleteDirectory(f);
				} else {
					if (!f.delete()) {
						f.deleteOnExit();
					}

				}
			}
		}
	}

	/**
	 * Recursively delete the contents of the specified folder if the filter accepts them.
	 */
	public static void deleteDirectoryContentsIf(final File folder, final FileFilter filter) {
		final File[] files = folder.listFiles();
		if (files != null) {
			// some JVMs return null for empty dirs
			for (final File f : files) {
				final boolean shouldDelete = filter.accept(f);
				if (f.isDirectory()) {
					if (shouldDelete) {
						deleteDirectory(f);
					} else {
						deleteDirectoryContentsIf(f, filter);
					}
				} else if (shouldDelete) {
					f.delete();
				}
			}
		}
	}

	/**
	 * Generate a String containing an alphabetical sequence based on a fixed index.
	 *
	 * Note: Performs poorly for very long sequences.
	 *
	 * @param i
	 *            the index of the sequence. Must be larger 0 or you get the empty string.
	 * @return 0 -> A, 1 -> B, 2 -> C, ... 25 -> Z, 26 -> AA, 27 -> AB, ... , 700 -> ZY, 701 -> ZZ, 702 -> AAA, ...
	 *
	 */
	public static String alphabeticalSequence(final int i) {
		return i < 0 ? "" : alphabeticalSequence((i / 26) - 1) + (char) (65 + i % 26);
	}

	public static String getStackTrace(final Throwable t) {
		return getStackTrace("", t);
	}

	public static String getStackTrace(final String indent, final Throwable t) {
		final StringBuilder sb = new StringBuilder();
		for (final StackTraceElement elem : t.getStackTrace()) {
			sb.append(indent);
			sb.append(String.format("%s%n", elem.toString()));
		}
		return sb.toString();
	}

	/**
	 * Repeat the string s for n times
	 */
	public static String repeat(final int n, final String s) {
		if (n == 0) {
			return "";
		}
		if (n < 0) {
			throw new IllegalArgumentException("n smaller than zero");
		}
		return new String(new char[n]).replace("\0", s);
	}

	@FunctionalInterface
	public interface IReduce<T, K> {
		T reduce(K entry);
	}

	@FunctionalInterface
	public interface IMapReduce<T, K> {
		T reduce(T lastValue, K entry);
	}

	@FunctionalInterface
	private interface IWriterConsumer {
		void consume(Writer fw) throws IOException;
	}
}
