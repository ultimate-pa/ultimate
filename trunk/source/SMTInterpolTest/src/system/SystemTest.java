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
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;
import org.osgi.framework.Bundle;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

@RunWith(JUnit4.class)
public class SystemTest {

	@Test
	public void testSystem() throws URISyntaxException, IOException {
		final Bundle bundle = Platform.getBundle("SMTInterpolTest");
		final URL fileURL = bundle.getEntry("test/");
		final File testDir = new File(FileLocator.resolve(fileURL).toURI());
		final File[] lst = testDir.listFiles();
		if (lst == null || lst.length == 0) {
			throw new IllegalArgumentException("could not locate SMT scripts");
		}

		for (final File dir : lst) {
			for (final File tst : dir
					.listFiles((dir1, name) -> name.endsWith(".smt2") && !name.endsWith(".msat.smt2"))) {
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

}
