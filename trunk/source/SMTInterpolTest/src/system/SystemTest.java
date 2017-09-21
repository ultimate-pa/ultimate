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
import java.net.URISyntaxException;
import java.net.URL;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

@RunWith(JUnit4.class)
public class SystemTest {

	private void performTest(final File f) throws SMTLIBException, FileNotFoundException {
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

	private boolean shouldExecute(final File f) {
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

	@Test
	public void testSystem() throws URISyntaxException, FileNotFoundException {
		final String name = getClass().getPackage().getName();
		final URL url = getClass().getClassLoader().getResource(name);
		final File f = new File(url.toURI());
		File[] lst = f.getParentFile().getParentFile().listFiles((FilenameFilter) (dir, name1) -> name1.equals("test"));
		if (lst == null || lst.length != 1) {
			return;
		}
		final File testDir = lst[0];
		lst = testDir.listFiles();
		for (final File dir : lst) {
			for (final File tst : dir.listFiles(
					(FilenameFilter) (dir1, name1) -> name1.endsWith(".smt2") && !name1.endsWith(".msat.smt2"))) {
				try {
					if (shouldExecute(tst)) {
						performTest(tst);
					}
				} catch (final SMTLIBException e) {
					Assert.fail("File " + tst.getAbsolutePath() + " produced error:\n" + e.getMessage());
				}
			}
		}
	}

}
