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
package de.uni_freiburg.informatik.ultimate.test.benchexec;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.StringWriter;
import java.net.MalformedURLException;
import java.net.URL;

import javax.xml.XMLConstants;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.namespace.QName;
import javax.xml.validation.SchemaFactory;

import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Benchmark;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.ObjectFactory;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BenchmarkSerializer {

	private static final String BENCHMARK_PACKAGE = Benchmark.class.getPackage().getName();
	private static final String BENCHMARK_URI = "/" + BENCHMARK_PACKAGE.replace(".", "/") + "/benchmark-1.9.xsd";
	private final static QName QNAME_BENCHMARK = new QName("", "benchmark");

	private BenchmarkSerializer() {
		// do not instantiate utility class
	}

	/**
	 * Convert a file to a {@link Benchmark} object if possible.
	 *
	 * @param xmlfile
	 *            The absolute path to the xml file.
	 * @return A {@link Benchmark} instance representing the file content.
	 *
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 * @throws SAXException
	 * @throws MalformedURLException
	 */
	public static Benchmark loadValidatedBenchmark(final String xmlfile)
			throws JAXBException, FileNotFoundException, SAXException {
		final JAXBContext jc = JAXBContext.newInstance(BENCHMARK_PACKAGE);
		final Unmarshaller unmarshaller = jc.createUnmarshaller();
		final URL fullPathString = BenchmarkSerializer.class.getResource(BENCHMARK_URI);
		unmarshaller.setSchema(SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI).newSchema(fullPathString));

		final Object unmarshalled = unmarshaller.unmarshal(new FileInputStream(xmlfile));

		return (Benchmark) unmarshalled;
	}

	/**
	 * This method saves a {@link Benchmark} instance to a valid xml file.
	 *
	 * @param xmlfile
	 *            The path to which the {@link Benchmark} should be saved.
	 * @param benchmarkInstance
	 *            The {@link Benchmark} instanceF.
	 *
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 */
	public static void saveBenchmark(final String xmlfile, final Benchmark benchmarkInstance)
			throws JAXBException, FileNotFoundException {
		final JAXBElement<Benchmark> jaxbelem =
				new JAXBElement<>(QNAME_BENCHMARK, Benchmark.class, null, benchmarkInstance);
		final ClassLoader cl = ObjectFactory.class.getClassLoader();
		final JAXBContext jc = JAXBContext.newInstance(BENCHMARK_PACKAGE, cl);
		final Marshaller marshaller = jc.createMarshaller();
		marshaller.setProperty("jaxb.formatted.output", true);
		marshaller.marshal(jaxbelem, new FileOutputStream(xmlfile));
	}

	public static String toString(final Benchmark benchmarkInstance) throws JAXBException {
		final JAXBElement<Benchmark> jaxbelem =
				new JAXBElement<>(QNAME_BENCHMARK, Benchmark.class, null, benchmarkInstance);
		final ClassLoader cl = ObjectFactory.class.getClassLoader();
		final JAXBContext jc = JAXBContext.newInstance(BENCHMARK_PACKAGE, cl);
		final Marshaller marshaller = jc.createMarshaller();
		marshaller.setProperty("jaxb.formatted.output", true);
		final StringWriter sw = new StringWriter();
		marshaller.marshal(jaxbelem, sw);
		return sw.toString();
	}

}
