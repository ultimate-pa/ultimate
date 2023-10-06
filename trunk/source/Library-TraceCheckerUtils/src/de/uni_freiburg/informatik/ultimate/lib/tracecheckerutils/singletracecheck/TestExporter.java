package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.math.BigInteger;
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

		FileOutputStream output;
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
		writeXml(createXML(testV.values), output);
		if (testV.need64Bit) {
			output = new FileOutputStream("test-suite/" + name + "64bit" + ".xml");
			writeXml(createXML(testV.values64Bit), output);
		}
	}

	public static final TestExporter getInstance() {
		if (instance == null) {
			instance = new TestExporter();
		}
		return instance;
	}

	// TODO split exportation and creation of the testvectors. Means
	final Document createXML(final LinkedList<String> inputs) throws ParserConfigurationException {

		// instance of a DocumentBuilderFactory
		final DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();

		// use factory to get an instance of document builder
		final DocumentBuilder db = dbf.newDocumentBuilder();
		// create instance of DOM
		final Document dom = db.newDocument();

		// create the root element
		final Element rootEle = dom.createElement("testcase");

		// create data elements and place them under root

		for (final String valueString : inputs) {
			if (valueString != null) {
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

	final LinkedList<String> values = new LinkedList<>();
	final LinkedList<String> values64Bit = new LinkedList<>();
	final LinkedList<String> valuesWithNegativeIndices = new LinkedList<>();
	final LinkedList<String> valuesWithPositiveIndices = new LinkedList<>();
	int countNonDets = 0;
	boolean need64Bit = false;

	public void addValueAssignment(final Term value, final int position, final String type) {
		if (position < 0) {
			throw new UnsupportedOperationException("Negative Position fo NonDet in SSA");
			// addNegativPositionToLinkedList(valuesWithNegativeIndices, position, value);
		} else {
			countNonDets += 1;
			addToLinkedList(position, value, type);
			if (need64Bit) {
				addToLinkedList64Bit(position, value, type);
			}

			// addToLinkedList(valuesWithPositiveIndices, position, value);
		}

	}

	private void addToLinkedList64Bit(final Integer index, final Term valueTerm, final String type) {
		need64Bit = false;
		if (values64Bit.size() < index) {
			for (int i = values64Bit.size(); i < index; i = i + 1) {
				values64Bit.add(null);
			}
		}
		String valueInRange = null;
		switch (valueTerm.getSort().getName()) {
		case SmtSortUtils.FLOATINGPOINT_SORT: {
			assert valueTerm instanceof ApplicationTerm;
			final ApplicationTerm cva = (ApplicationTerm) valueTerm;
			String sign = cva.getParameters()[0].toStringDirect();
			sign = sign.replaceAll("[^01]", "");

			String exponent = cva.getParameters()[1].toStringDirect();
			exponent = exponent.replaceAll("[^01]", "");

			String significant = cva.getParameters()[2].toStringDirect();
			significant = significant.replaceAll("[^01]", "");

			final String floatAsBitString = sign + exponent + significant;
			final int intBits = (int) Long.parseLong(floatAsBitString, 2);
			final float myFloat = Float.intBitsToFloat(intBits);

			valueInRange = myFloat + "";
			break;
		}
		case SmtSortUtils.BITVECTOR_SORT: {
			final Matcher m = Pattern.compile("\\(_\\sbv(\\d+)\\s\\d+\\)").matcher(valueTerm.toStringDirect());
			m.find();
			valueInRange = m.group(1);
			if (type.equals("int") || type.equals("long")) { // if signed

				if (SmtSortUtils.getBitvectorLength(valueTerm.getSort()) <= 64) {
					final BigInteger value = new BigInteger(valueInRange);
					if (value.compareTo(new BigInteger("9223372036854775807")) == 1) {
						// wenn 2147483648 dann -2,147,483,648
						final BigInteger newValue = new BigInteger("-9223372036854775808")
								.add((value.subtract(new BigInteger("9223372036854775808"))));

						valueInRange = String.valueOf(newValue);
					}
				}
			}
			break;
		}
		case SmtSortUtils.REAL_SORT: {
			if (type.equals("float") || type.equals("double")) {
				valueInRange = valueTerm.toStringDirect().replaceAll("[\\(\\)\\s]", "");

				break;
			}
		}
		case SmtSortUtils.INT_SORT: {

			valueInRange = valueTerm.toStringDirect().replaceAll("[\\(\\)\\s]", "");
			final BigInteger value = new BigInteger(valueInRange);

			switch (type) {
			case "short": {
				// -32,768 to 32,767
				if (value.compareTo(new BigInteger("32767")) == 1) {
					final BigInteger newValue = value.mod(new BigInteger("32768"));
					valueInRange = String.valueOf(newValue);
				} else if (value.compareTo(new BigInteger("-32768")) == -1) {
					final BigInteger newValue = value.mod(new BigInteger("32768"));
					valueInRange = String.valueOf(newValue.negate());
				}
				break;
			}
			case "ushort": {
				// 0 to 65,535
				final BigInteger newValue = value.mod(new BigInteger("65536"));
				valueInRange = String.valueOf(newValue);

				break;
			}
			case "int": {
				if (value.compareTo(new BigInteger("2147483647")) == 1) {
					final BigInteger newValue = value.mod(new BigInteger("2147483648"));
					valueInRange = String.valueOf(newValue);
				} else if (value.compareTo(new BigInteger("-2147483648")) == -1) {
					final BigInteger newValue = value.mod(new BigInteger("2147483648"));
					valueInRange = String.valueOf(newValue.negate());
				}
				break;
			}
			case "long": {
				if (value.compareTo(new BigInteger("9223372036854775807")) == 1) {
					final BigInteger newValue = value.mod(new BigInteger("9223372036854775808"));
					valueInRange = String.valueOf(newValue);
				} else if (value.compareTo(new BigInteger("-9223372036854775808")) == -1) {
					final BigInteger newValue = value.mod(new BigInteger("9223372036854775808"));
					valueInRange = String.valueOf(newValue.negate());
				}
				break;
			}
			case "uint": {
				final BigInteger newValue = value.mod(new BigInteger("4294967296"));
				valueInRange = String.valueOf(newValue);
				break;
			}
			case "ulong": {
				final BigInteger newValue = value.mod(new BigInteger("18446744073709551616"));
				valueInRange = String.valueOf(newValue);
				break;
			}
			case "ulonglong": {
				final BigInteger newValue = value.mod(new BigInteger("18446744073709551616"));
				valueInRange = String.valueOf(newValue);
				break;
			}
			case "char": {
				if (value.compareTo(new BigInteger("127")) == 1) {
					final BigInteger newValue = value.mod(new BigInteger("128"));
					valueInRange = String.valueOf(newValue);
				} else if (value.compareTo(new BigInteger("-128")) == -1) {
					final BigInteger newValue = value.mod(new BigInteger("128"));
					valueInRange = String.valueOf(newValue.negate());
				}
				break;
			}
			case "uchar": {
				final BigInteger newValue = value.mod(new BigInteger("256"));
				valueInRange = String.valueOf(newValue);
				break;
			}
			default:
			}
			break;
		}

		default: {
			throw new AssertionError("Unexpected Sort For Test Output");
		}
		}

		values64Bit.add(index, valueInRange);

	}

	private void addToLinkedList(final Integer index, final Term valueTerm, final String type) {
		if (values.size() < index) {
			for (int i = values.size(); i < index; i = i + 1) {
				values.add(null);
			}
		}

		String valueInRange = null;
		switch (valueTerm.getSort().getName()) {
		case SmtSortUtils.FLOATINGPOINT_SORT: {
			if (type.equals("float")) {
				if (((ApplicationTerm) valueTerm).getParameters().length == 3) {
					assert valueTerm instanceof ApplicationTerm;
					final ApplicationTerm cva = (ApplicationTerm) valueTerm;
					String sign = cva.getParameters()[0].toStringDirect();
					sign = sign.replaceAll("[^01]", "");

					String exponent = cva.getParameters()[1].toStringDirect();
					exponent = exponent.replaceAll("[^01]", "");

					String significant = cva.getParameters()[2].toStringDirect();
					significant = significant.replaceAll("[^01]", "");
					final String floatAsBitString = sign + exponent + significant;
					// final int intBits = Integer.parseInt(floatAsBitString, 2);
					final int intBits = (int) Long.parseLong(floatAsBitString, 2);
					final float asFloat = Float.intBitsToFloat(intBits);
					valueInRange = asFloat + "";
					break;
				} else {
					if (valueTerm.toStringDirect().contains("+oo")) {
						valueInRange = Float.POSITIVE_INFINITY + "";
					} else if (valueTerm.toStringDirect().contains("-oo")) {
						valueInRange = Float.NEGATIVE_INFINITY + "";
					} else if (valueTerm.toStringDirect().contains("NaN")) {
						valueInRange = Float.NaN + "";
					} else if (valueTerm.toStringDirect().contains("zero")) {
						valueInRange = "0";
					} else {
						throw new AssertionError("Unexpected Sort For Output Type");
					}
					break;
				}
			} else if (type.equals("double")) {
				assert valueTerm instanceof ApplicationTerm;
				if (((ApplicationTerm) valueTerm).getParameters().length == 3) {
					final ApplicationTerm cva = (ApplicationTerm) valueTerm;
					String sign = cva.getParameters()[0].toStringDirect();
					sign = sign.replaceAll("[^01]", "");

					String exponent = cva.getParameters()[1].toStringDirect();
					exponent = exponent.replaceAll("[^01]", "");

					String significant = cva.getParameters()[2].toStringDirect();
					significant = significant.replaceAll("[^01]", "");
					final String floatAsBitString = sign + exponent + significant;
					final long longBits = (new BigInteger(floatAsBitString, 2)).longValue();
					final double asDouble = Double.longBitsToDouble(longBits);
					valueInRange = asDouble + "";
					break;
				} else {
					if (valueTerm.toStringDirect().contains("+oo")) {
						valueInRange = Double.POSITIVE_INFINITY + "";
					} else if (valueTerm.toStringDirect().contains("-oo")) {
						valueInRange = Double.NEGATIVE_INFINITY + "";
					} else if (valueTerm.toStringDirect().contains("NaN")) {
						valueInRange = Double.NaN + "";
					} else if (valueTerm.toStringDirect().contains("zero")) {
						valueInRange = "0";
					} else {
						throw new AssertionError("Unexpected Sort For Output Type");
					}
					break;
				}
			} else {
				throw new AssertionError("Unexpected Sort For Output Type");
			}

		}
		case SmtSortUtils.BITVECTOR_SORT: {
			final Matcher m = Pattern.compile("\\(_\\sbv(\\d+)\\s\\d+\\)").matcher(valueTerm.toStringDirect());
			m.find();
			valueInRange = m.group(1);
			if (type.equals("int") || type.equals("long")) { // if signed
				if (SmtSortUtils.getBitvectorLength(valueTerm.getSort()) <= 32) {
					final BigInteger value = new BigInteger(valueInRange);
					if (value.compareTo(new BigInteger("2147483647")) == 1) {
						// wenn 2147483648 dann -2,147,483,648
						final BigInteger newValue =
								new BigInteger("-2147483648").add((value.subtract(new BigInteger("2147483648"))));
						valueInRange = String.valueOf(newValue);
					}
				} else {
					need64Bit = true;
				}
			} else if (type.equals("char")) {
				final BigInteger value = new BigInteger(valueInRange);
				if (value.compareTo(new BigInteger("32767")) == 1) {
					final BigInteger newValue = new BigInteger("-32768").add((value.subtract(new BigInteger("32768"))));
					valueInRange = String.valueOf(newValue);
				}
			} else if (type.equals("short")) {
				final BigInteger value = new BigInteger(valueInRange);
				if (value.compareTo(new BigInteger("127")) == 1) {
					final BigInteger newValue = new BigInteger("-128").add((value.subtract(new BigInteger("128"))));
					valueInRange = String.valueOf(newValue);
				}
				throw new AssertionError("Unexpected Sort For Output Type");
			}
			break;
		}
		case SmtSortUtils.REAL_SORT: {
			if (type.equals("float") || type.equals("double")) {
				valueInRange = valueTerm.toStringDirect().replaceAll("[\\(\\)\\s]", "");
				break;
			}
		}
		case SmtSortUtils.INT_SORT: {
			valueInRange = valueTerm.toStringDirect().replaceAll("[\\(\\)\\s]", "");
			final BigInteger value = new BigInteger(valueInRange);
			if (type.equals("long")) {
				if (value.compareTo(new BigInteger("2147483647")) == 1) {
					need64Bit = true;
				} else if (value.compareTo(new BigInteger("-2147483648")) == -1) {
					need64Bit = true;
				}
			} else if (type.equals("ulong")) {
				if (value.compareTo(new BigInteger("4294967295")) == 1) {
					need64Bit = true;
				}
			}

			switch (type) {
			case "short": {
				// -32,768 to 32,767
				if (value.compareTo(new BigInteger("32767")) == 1) {
					final BigInteger newValue = value.mod(new BigInteger("32768"));
					valueInRange = String.valueOf(newValue);
				} else if (value.compareTo(new BigInteger("-32768")) == -1) {
					final BigInteger newValue = value.mod(new BigInteger("32768"));
					valueInRange = String.valueOf(newValue.negate());
				}
				break;
			}
			case "ushort": {
				// 0 to 65,535
				final BigInteger newValue = value.mod(new BigInteger("65536"));
				valueInRange = String.valueOf(newValue);

				break;
			}
			case "int":
			case "long": {
				if (value.compareTo(new BigInteger("2147483647")) == 1) {
					final BigInteger newValue = value.mod(new BigInteger("2147483648"));
					valueInRange = String.valueOf(newValue);
				} else if (value.compareTo(new BigInteger("-2147483648")) == -1) {
					final BigInteger newValue = value.mod(new BigInteger("2147483648"));
					valueInRange = String.valueOf(newValue.negate());
				}
				break;
			}
			case "uint":
			case "ulong": {
				final BigInteger newValue = value.mod(new BigInteger("4294967296"));
				valueInRange = String.valueOf(newValue);
				break;
			}
			case "ulonglong": {
				final BigInteger newValue = value.mod(new BigInteger("18446744073709551616"));
				valueInRange = String.valueOf(newValue);
				break;
			}
			case "char": {
				if (value.compareTo(new BigInteger("127")) == 1) {
					final BigInteger newValue = value.mod(new BigInteger("128"));
					valueInRange = String.valueOf(newValue);
				} else if (value.compareTo(new BigInteger("-128")) == -1) {
					final BigInteger newValue = value.mod(new BigInteger("128"));
					valueInRange = String.valueOf(newValue.negate());
				}
				break;
			}
			case "uchar": {
				final BigInteger newValue = value.mod(new BigInteger("256"));
				valueInRange = String.valueOf(newValue);
				break;
			}
			default:

			}
			break;
		}

		default: {
			throw new AssertionError("Unexpected Sort For Test Output");
		}
		}

		values.add(index, valueInRange);

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

	public String getNonDetTypeFromName(final String payload) {
		final Matcher m = Pattern.compile("__VERIFIER_nondet_(\\w*)").matcher(payload);
		m.find();

		return m.group(1);

	}
}
