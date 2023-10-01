package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;
import org.w3c.dom.DocumentType;
import org.w3c.dom.Element;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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

		final FileOutputStream output;
		final String name = "testcase" + i;
		final boolean noDirectories = false;
		final boolean allInOneDirecotry = true;
		if (noDirectories) {
			output = new FileOutputStream(name + ".xml");
		} else if (allInOneDirecotry) {
			Files.createDirectories(Paths.get("test-suite"));
			output = new FileOutputStream("test-suite/" + name + ".xml");
		} else { // testsuites directory and subdirectory for every program that contains the tests
			if (!foundMakefileAndDir) {
				findMakeFileAndDir();
			}
			if (mDirName == null) {
				Files.createDirectories(Paths.get("testsuites"));

				output = new FileOutputStream("testsuites/" + name + ".xml");
			} else {
				Files.createDirectories(Paths.get(mDirName));
				output = new FileOutputStream("testsuites/" + name + ".xml");
			}
		}
		writeXml(createXML(testV), output); // TODO Setting
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
		final Element rootEle = dom.createElement("testcase");

		// create data elements and place them under root
		String valueString = null;
		for (final Term va : tv.values) {
			if (va != null) {
				switch (va.getSort().getName()) {
				case SmtSortUtils.FLOATINGPOINT_SORT: {
					assert va instanceof ApplicationTerm;
					final ApplicationTerm cva = (ApplicationTerm) va;

					String sign = cva.getParameters()[0].toStringDirect();
					sign = sign.replaceAll("[^01]", "");

					String exponent = cva.getParameters()[1].toStringDirect();
					exponent = exponent.replaceAll("[^01]", "");

					String significant = cva.getParameters()[2].toStringDirect();
					significant = significant.replaceAll("[^01]", "");

					final String floatAsBitString = sign + exponent + significant;
					final int intBits = (int) Long.parseLong(floatAsBitString, 2);
					final float myFloat = Float.intBitsToFloat(intBits);

					valueString = myFloat + "";
					break;
				}
				case SmtSortUtils.BITVECTOR_SORT: {
					final Matcher m = Pattern.compile("\\(_\\sbv(\\d+)\\s\\d+\\)").matcher(va.toStringDirect());
					valueString = m.group();
					break;
				}
				case SmtSortUtils.INT_SORT: {
					valueString = va.toStringDirect().replaceAll("[\\(\\)\\s]", "");
					break;
				}
				case SmtSortUtils.REAL_SORT: {
					valueString = va.toStringDirect().replaceAll("[\\(\\)\\s]", "");
					break;
				}
				// case SmtSortUtils.BOOL_SORT: {
				// if (SmtUtils.isTrueLiteral(va)) {
				// valueString = "1";
				// } else {
				// valueString = "0";
				// }
				// break;
				// }
				default: {
					throw new AssertionError("Unexpected Sort For Test Output");
				}
				}

				final Element element = dom.createElement("input");

				element.appendChild(dom.createTextNode(valueString));
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
		final DOMImplementation domImpl = doc.getImplementation();
		final DocumentType doctype =
				domImpl.createDocumentType("testcase", "+//IDN sosy-lab.org//DTD test-format testcase 1.1//EN",
						"https://sosy-lab.org/test-format/testcase-1.1.dtd");
		transformer.setOutputProperty(OutputKeys.DOCTYPE_PUBLIC, doctype.getPublicId());
		transformer.setOutputProperty(OutputKeys.DOCTYPE_SYSTEM, doctype.getSystemId());
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
	final LinkedList<Term> valuesWithNegativeIndices = new LinkedList<>();
	final LinkedList<Term> valuesWithPositiveIndices = new LinkedList<>();
	int countNonDets = 0;

	public void addValueAssignment(final Term value, final int position) {
		if (position < 0) {
			throw new UnsupportedOperationException("Negative Position fo NonDet in SSA");
			// addNegativPositionToLinkedList(valuesWithNegativeIndices, position, value);
		} else {
			countNonDets += 1;
			addToLinkedList(values, position, value);
			// addToLinkedList(valuesWithPositiveIndices, position, value);
		}

	}

	private void addToLinkedList(final LinkedList<Term> testVector, final Integer index, final Term t) {
		if (testVector.size() < index) {
			for (int i = testVector.size(); i < index; i = i + 1) {
				testVector.add(null);
			}
		}
		testVector.add(index, t);
	}

	private void addNegativPositionToLinkedList(final LinkedList<Term> testVector, final Integer index, final Term t) {
		assert index < 0;
		testVector.add(t);
	}

	public boolean isEmpty() {
		return values.isEmpty();
	}

	public void addValuesWithNegativeIndex() {
		values.addAll(valuesWithNegativeIndices);
		values.addAll(valuesWithPositiveIndices);
	}
}
