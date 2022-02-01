/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.util;

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBException;

import org.junit.Assert;
import org.junit.Test;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.test.benchexec.BenchmarkSerializer;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Benchmark;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Rundefinition;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Tasks;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RundefinitionTest {

	@Test
	public void serializeAndDeserialize() {

		final Benchmark bench = new Benchmark();
		bench.setTool("TestTool");

		final Rundefinition rundef = new Rundefinition();
		bench.getRundefinitionOrOptionOrPropertyfile().add(rundef);
		rundef.setName("TestRundef");
		final Tasks tasks = new Tasks();
		tasks.setName("TestTask");

		bench.getRundefinitionOrOptionOrPropertyfile().add(tasks);

		try {
			final File tmpFile = File.createTempFile("rundef", ".xml");
			BenchmarkSerializer.saveBenchmark(tmpFile.getAbsolutePath(), bench);
			final String fileContent =
					Files.readAllLines(Paths.get(tmpFile.getAbsolutePath()), Charset.defaultCharset()).stream()
							.collect(Collectors.joining("\n"));
			System.out.println(fileContent);

			final Benchmark deserializedRundef = BenchmarkSerializer.loadValidatedBenchmark(tmpFile.getAbsolutePath());

			Assert.assertNotNull(deserializedRundef);
			Assert.assertEquals(rundef.getName(),
					((Rundefinition) deserializedRundef.getRundefinitionOrOptionOrPropertyfile().get(0)).getName());
		} catch (final IOException | JAXBException | SAXException e) {
			e.printStackTrace();
			Assert.assertTrue(false);
		}

	}

}
