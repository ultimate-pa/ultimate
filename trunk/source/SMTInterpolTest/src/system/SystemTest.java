/*
 * Copyright (C) 2012-2013 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package system;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FilenameFilter;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import org.eclipse.core.runtime.FileLocator;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

@RunWith(Parameterized.class)
public class SystemTest {

	public File mFile;

	public SystemTest(final File file) {
		mFile = file;
	}

	@Test
	public void testSystem() throws FileNotFoundException {
		performTest(mFile);
	}

	private static void performTest(final File f) throws SMTLIBException, FileNotFoundException {
		System.out.println("Testing " + f.getAbsolutePath());
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);
		final SMTInterpol solver = new SMTInterpol(options);
		final ParseEnvironment pe = new ParseEnvironment(solver, options) {

			@Override
			public void printError(final String message) {
				Assert.fail(f.getAbsolutePath() + ": " + message);
			}

			@Override
			public void printResponse(final Object response) {
				if ("unsupported".equals(response)) {
					Assert.fail(f.getAbsolutePath() + ": " + "unsupported");
				}
				super.printResponse(response);
			}

		};
		pe.parseStream(new FileReader(f), "TestStream");
	}

	private static boolean shouldExecute(final File f) {
		final String fname = f.getName();
		if (fname.startsWith("tightrhombus-lira")) {
			// remove tightrhombus-lira-xxx-yyy-
			String sizestr = fname.substring(26, 28); // NOCHECKSTYLE
			if (sizestr.length() == 2 && !Character.isDigit(sizestr.charAt(1))) {
				sizestr = sizestr.substring(0, 1);
			}
			final int size = Integer.parseInt(sizestr);
			return size < 5;// NOCHECKSTYLE
		} else if (fname.startsWith("tightrhombus")) {
			String sizestr = fname.substring(21, 23); // NOCHECKSTYLE
			if (sizestr.length() == 2 && !Character.isDigit(sizestr.charAt(1))) {
				sizestr = sizestr.substring(0, 1);
			}
			final int size = Integer.parseInt(sizestr);
			return size < 5;// NOCHECKSTYLE
		}
		return true;
	}

	@Parameters(name = "{0}")
	public static Collection<File> testFiles() throws URISyntaxException, IOException {

		final Collection<File> testFiles = new ArrayList<>();

		final String name = SystemTest.class.getPackage().getName();
		final URL url = SystemTest.class.getClassLoader().getResource(name);
		try {
			final String protocol = url.getProtocol();
			final File f;
			if ("file".equals(protocol)) {
				f = new File(url.toURI());
			} else if ("bundleresource".equals(protocol)) {
				f = new File(FileLocator.toFileURL(url).getFile());
			} else {
				throw new UnsupportedOperationException("unsupported resource protocol");
			}

			// find directory named test below SMTInterpolTest and above f
			final FilenameFilter filter = (FilenameFilter) (dir, name1) -> name1.equals("test");
			File parent = f.getParentFile();
			File[] lst = null;
			while (parent != null) {
				lst = parent.listFiles(filter);
				if (lst != null && lst.length > 0) {
					break;
				}
				parent = parent.getParentFile();
			}
			assert lst != null && lst.length > 0 : "Could not find any tests starting from File " + f.getAbsolutePath();

			final ArrayDeque<File> todo = new ArrayDeque<>();
			if (lst.length > 1) {
				System.out.println("More than one test directory found");
			}
			todo.addAll(Arrays.asList(lst));
			while (!todo.isEmpty()) {
				final File file = todo.removeFirst();
				if (file.isDirectory()) {
					for (final File subFile : file.listFiles()) {
						todo.add(subFile);
					}
				} else if (file.getName().endsWith(".smt2") && !file.getName().endsWith(".msat.smt2")) {
					if (shouldExecute(file)) {
						testFiles.add(file);
					}
				}
			}
			return testFiles;
		} catch (final Throwable t) {
			if (url != null) {
				System.out.println("Error trying to extract system tests from URL " + url.toString());
			} else {
				System.out.println("Error trying to extract system tests; could not load resource");
			}

			t.printStackTrace();
			throw t;
		}
	}

}
