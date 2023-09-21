/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 *
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Paths;

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

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;

/**
 *
 * @author Max Barth max.barth95@gmx.de
 *
 */
public class TestCompMetaFilePrinter<TTE, TE> extends BaseWitnessGenerator<TTE, TE> {

	private static final String[] ACSL_SUBSTRING = new String[] { "\\old", "\\result", "\\exists" };

	private final ILogger mLogger;
	private final IBacktranslationValueProvider<TTE, TE> mStringProvider;
	private final IBacktranslatedCFG<?, TTE> mTranslatedCFG;
	private final boolean mIsACSLForbidden;
	IUltimateServiceProvider mServices;

	@SuppressWarnings("unchecked")
	public TestCompMetaFilePrinter(final IBacktranslatedCFG<?, TTE> translatedCFG, final ILogger logger,
			final IUltimateServiceProvider services) throws Exception {
		super(services);
		mLogger = logger;
		mStringProvider = (IBacktranslationValueProvider<TTE, TE>) translatedCFG.getBacktranslationValueProvider();
		mTranslatedCFG = translatedCFG;
		mIsACSLForbidden =
				PreferenceInitializer.getPreferences(services).getBoolean(PreferenceInitializer.LABEL_DO_NOT_USE_ACSL);
		mServices = services;

	}

	public void printMetaFile() throws Exception {
		final boolean noDirectories = false;
		final boolean allInOneDirecotry = true;
		try {
			final FileOutputStream output;
			if (noDirectories) {
				output = new FileOutputStream("metadata.xml");
			} else if (allInOneDirecotry) {
				Files.createDirectories(Paths.get("test-suite"));
				output = new FileOutputStream("test-suite/metadata.xml");
			} else {
				final String outputDir = "testsuite_" + mTranslatedCFG.getFilename().substring(
						mTranslatedCFG.getFilename().lastIndexOf("\\") + 1, mTranslatedCFG.getFilename().length() - 2);

				Files.createDirectories(Paths.get("tests"));
				Files.createDirectories(Paths.get("tests/testsuite_" + outputDir));
				output = new FileOutputStream("tests/testsuite_" + outputDir + "/metadata.xml");
			}
			writeXml(createXML(), output);
		} catch (final IOException | TransformerException | ParserConfigurationException e) {
			throw e;
		}
	}

	public Document createXML() throws ParserConfigurationException {

		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		// instance of a DocumentBuilderFactory
		final DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();

		// use factory to get an instance of document builder
		final DocumentBuilder db = dbf.newDocumentBuilder();
		// create instance of DOM
		final Document dom = db.newDocument();
		final Element rootEle = dom.createElement("test-metadata");

		// <!ELEMENT sourcecodelang (#PCDATA)>
		final Element sourcecodelang = dom.createElement("sourcecodelang");
		sourcecodelang.appendChild(dom.createTextNode("C")); // TODO
		rootEle.appendChild(sourcecodelang);

		// <!ELEMENT producer (#PCDATA)>
		final Element producer = dom.createElement("producer");
		producer.appendChild(dom.createTextNode(ups.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER)));
		rootEle.appendChild(producer);

		// <!ELEMENT specification (#PCDATA)>
		final Element specification = dom.createElement("specification");

		specification
				.appendChild(dom.createTextNode(ups.getString(PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION)));

		rootEle.appendChild(specification);

		// <!ELEMENT programfile (#PCDATA)>
		final Element programfile = dom.createElement("programfile");
		programfile.appendChild(dom.createTextNode(
				"./" + mTranslatedCFG.getFilename().substring(mTranslatedCFG.getFilename().lastIndexOf("\\") + 1)));
		rootEle.appendChild(programfile);

		// <!ELEMENT programhash (#PCDATA)>
		final Element programhash = dom.createElement("programhash");
		programhash.appendChild(dom.createTextNode(ups.getString(PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH)));
		rootEle.appendChild(programhash);

		// <!ELEMENT entryfunction (#PCDATA)>
		final Element entryfunction = dom.createElement("entryfunction");
		entryfunction.appendChild(dom.createTextNode("main")); // TODO
		rootEle.appendChild(entryfunction);

		// <!ELEMENT architecture (#PCDATA)>
		final Element architecture = dom.createElement("architecture");
		architecture
				.appendChild(dom.createTextNode(ups.getString(PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE)));
		rootEle.appendChild(architecture);

		// <!ELEMENT creationtime (#PCDATA)>
		final Element creationtime = dom.createElement("creationtime");
		creationtime.appendChild(dom.createTextNode(CoreUtil.getIsoUtcTimestamp()));
		rootEle.appendChild(creationtime);

		// <!ELEMENT inputtestsuitefile (#PCDATA)>
		// final Element inputtestsuitefile =
		// dom.createElement("inputtestsuitefile");
		// inputtestsuitefile.appendChild(dom.createTextNode());
		// rootEle.appendChild(inputtestsuitefile);

		// <!ELEMENT inputtestsuitehash (#PCDATA)>
		// final Element inputtestsuitehash =
		// dom.createElement("inputtestsuitehash");
		// inputtestsuitehash.appendChild(dom.createTextNode());
		// rootEle.appendChild(inputtestsuitehash);

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

	@Override
	public String makeGraphMLString() {
		// TODO Auto-generated method stub
		return null;
	}
}