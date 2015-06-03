package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.StringWriter;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.apache.log4j.Logger;
import org.apache.log4j.Priority;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ObjectFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExParserPreferenceInitializer;

/**
 * @author Marius Greitschus
 *
 */
public class SpaceExParser implements ISource {

	private String[] mFileTypes;
	private String[] mFileNames;
	private IUltimateServiceProvider mServices;
	private Logger mLogger;

	public SpaceExParser() {
		mFileTypes = new String[] { "xml" };
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() {
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new SpaceExParserPreferenceInitializer();
	}

	@Override
	public boolean parseable(File[] files) {
		for (File f : files) {
			if (!parseable(f)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean parseable(File file) {

		boolean known_extension = false;

		for (String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				known_extension = true;
				break;
			}
		}

		if (!known_extension) {
			return false;
		}

		// TODO Check for SpaceEx extension
		return true;
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IElement parseAST(File file) throws Exception {
		FileInputStream fis = new FileInputStream(file);

		JAXBContext jc = JAXBContext.newInstance(ObjectFactory.class);

		Unmarshaller unmarshaller = jc.createUnmarshaller();

		Sspaceex sx = (Sspaceex) unmarshaller.unmarshal(fis);

		Marshaller marshaller = jc.createMarshaller();

		marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);

		StringWriter sw = new StringWriter();
		
		marshaller.marshal(sx, sw);
		
		mLogger.info(sw.toString());

		return null;
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}

	@Override
	public GraphType getOutputDefinition() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setPreludeFile(File prelude) {
		// TODO Auto-generated method stub

	}

	public void ParseFile(File file) {
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();

		try {
			DocumentBuilder db = dbf.newDocumentBuilder();
			Document dom = db.parse(file.getAbsolutePath());

		} catch (ParserConfigurationException pce) {
			pce.printStackTrace();
		} catch (SAXException se) {
			se.printStackTrace();
		} catch (IOException ioe) {
			ioe.printStackTrace();
		}
	}

}
