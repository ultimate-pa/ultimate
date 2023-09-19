package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class TestExporter {

	private static final boolean WRITE_TESTCASES_TO_FILE = true;
	LinkedHashSet<TestVector> tvSet = new LinkedHashSet<>();
	private static TestExporter instance = null;
	private String mDirName = null;
	private boolean foundMakefileAndDir = false;
	private String pathToDir;

	/*
	 * Export Tests in:
	 * 1: one directory for all programs
	 * 2: one directory for each program
	 */
	public void exportTests(final TestVector testV, final int i, final boolean allInOneFile) throws Exception {
		if (!foundMakefileAndDir) {
			findMakeFileAndDir();
		}
		if (mDirName == null) {
			// useDefaultFodler;

			try {
				Files.createDirectories(Paths.get("testsuite"));

				final String name = "testcase" + i;

				final FileOutputStream output = new FileOutputStream("testsuite/" + name + ".xml");
				writeXml(createXML(testV), output); // TODO Setting
			} catch (final IOException e) {
				throw e;
			}
		} else {
			try {
				final String name = "testcase" + i;
				Files.createDirectories(Paths.get(mDirName));
				final FileOutputStream output = new FileOutputStream(mDirName + "/" + name + ".xml");
				writeXml(createXML(testV), output); // TODO Setting
			} catch (final IOException e) {
				throw e;
			}
		}

	}

	public static TestExporter getInstance() {
		if (instance == null) {
			instance = new TestExporter();
		}
		return instance;
	}

	// TODO split exportation and creation of the testvectors. Means
	private Document createXML(final TestVector tv) throws ParserConfigurationException {

		// instance of a DocumentBuilderFactory
		final DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();

		// use factory to get an instance of document builder
		final DocumentBuilder db = dbf.newDocumentBuilder();
		// create instance of DOM
		final Document dom = db.newDocument();

		// create the root element
		final Element rootEle = dom.createElement("testcases");

		// create data elements and place them under root

		for (final Term va : tv.values) {
			if (va != null) {
				final Element element = dom.createElement("input");
				element.appendChild(dom.createTextNode(va.toStringDirect()));
				rootEle.appendChild(element);
			}
		}

		dom.appendChild(rootEle);
		return dom;
	}

	// write doc to output stream
	private static void writeXml(final Document doc, final OutputStream output) throws TransformerException {

		final TransformerFactory transformerFactory = TransformerFactory.newInstance();
		final Transformer transformer = transformerFactory.newTransformer();
		// pretty print XML
		transformer.setOutputProperty(OutputKeys.INDENT, "yes");
		final DOMSource source = new DOMSource(doc);
		final StreamResult result = new StreamResult(output);

		transformer.transform(source, result);

	}

	public void addTvToSet(final TestVector tv) {
		tvSet.add(tv);
	}

	/*
	 * Can be Used to create one Dir for each program
	 */
	public void findMakeFileAndDir() {
		final File dir = new File("tests");
		final File[] files = dir.listFiles();
		final File lastModified = Arrays.stream(files).filter(File::isDirectory)
				.max(Comparator.comparing(File::lastModified)).orElse(null);
		mDirName = lastModified.toString();
		foundMakefileAndDir = true;
	}

}

class TestVector {

	final LinkedList<Term> values = new LinkedList<>();

	public void addValueAssignment(final Term value, final int position) {
		addToLinkedList(values, position, value);
	}

	private void addToLinkedList(final LinkedList<Term> testVector, final Integer index, final Term t) {
		if (testVector.size() < index) {
			for (int i = testVector.size(); i < index; i = i + 1) {
				testVector.add(null);
			}
		}
		testVector.add(index, t);
	}

	public boolean isEmpty() {
		return values.isEmpty();
	}
}
