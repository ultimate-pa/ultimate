package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.net.MalformedURLException;
import java.net.URL;

import javax.xml.XMLConstants;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import javax.xml.validation.SchemaFactory;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.services.ToolchainStorage;

/**
 * This implements the datastructure representing a Ultimate toolchain. It can
 * be used for constructing a Ultimate toolchain manually or from an XML
 * specification file.
 * 
 * @author Bj�rn Buchhold, Christian Simon
 * 
 */
public class ToolchainData {

	private ObjectFactory mObjectFactory;
	private ToolchainListType mToolchain;
	private ToolchainStorage mStorage;

	/**
	 * This constructor creates an empty toolchain.
	 */
	public ToolchainData() {
		mObjectFactory = new ObjectFactory();
		mToolchain = mObjectFactory.createToolchainListType();
		mStorage = new ToolchainStorage();
	}

	private boolean isReady(Bundle bundle) {
		return bundle != null
				&& (bundle.getState() & (Bundle.RESOLVED | Bundle.STARTING | Bundle.ACTIVE | Bundle.STOPPING)) != 0;
	}

	/**
	 * This constructor creates a toolchain from an XML file.
	 * 
	 * @param xmlfile
	 *            an xml file compliant with toolchain.xsd
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 * @throws SAXException
	 * @throws MalformedURLException
	 */
	@SuppressWarnings({ "unchecked" })
	public ToolchainData(String xmlfile) throws JAXBException, FileNotFoundException, SAXException {
		mObjectFactory = new ObjectFactory();
		JAXBContext jc = JAXBContext.newInstance("de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain");

		// all this effort just for validating the input XML file...
		Bundle bundle = Platform.getBundle(Activator.s_PLUGIN_ID);

		if (!isReady(bundle)) {
			System.err.println("Bundle not ready");
		}

		URL fullPathString = FileLocator.find(bundle, new Path(
				"src/de/uni_freiburg/informatik/ultimate/core/coreplugin/toolchain/toolchain.xsd"), null);
		if (fullPathString == null) {
			try {
				fullPathString = new URL(
						"src/de/uni_freiburg/informatik/ultimate/core/coreplugin/toolchain/toolchain.xsd");
			} catch (MalformedURLException e) {
				e.printStackTrace();
			}
		}

		Unmarshaller u = jc.createUnmarshaller();
		u.setSchema(SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI).newSchema(fullPathString));

		JAXBElement<ToolchainListType> doc = (JAXBElement<ToolchainListType>) u.unmarshal(new FileInputStream(xmlfile));

		mToolchain = doc.getValue();
		mStorage = new ToolchainStorage();
	}

	/**
	 * This method marshals a toolchain into an xml file.
	 * 
	 * @param xmlfile
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 */
	public void writeToFile(String xmlfile) throws JAXBException, FileNotFoundException {
		JAXBContext jc = JAXBContext.newInstance("de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain");
		JAXBElement<ToolchainListType> newdoc = mObjectFactory.createToolchain(this.mToolchain);
		Marshaller m = jc.createMarshaller();
		m.marshal(newdoc, new FileOutputStream(xmlfile));
	}

	/**
	 * This method adds a Plugin to the Toolchain. The plugin object must have
	 * been previously instantiated using ObjectFactory.
	 * 
	 * @param plugin
	 *            object of type PluginType
	 */
	public void addPlugin(PluginType plugin) {
		mToolchain.getPluginOrSubchain().add(plugin);
	}

	/**
	 * This method adds a plugin / tool to the toolchain by creating a new
	 * plugin object from a plugin name first.
	 * 
	 * @param name
	 *            of the desired plugin
	 */
	public void addPlugin(String name) {
		PluginType foo = new PluginType();
		foo.setId(name);
		mToolchain.getPluginOrSubchain().add(foo);
	}

	/**
	 * This method adds a Subchain to the Toolchain. The subchain object must
	 * have been previously instantiated using ObjectFactory.
	 * 
	 * @param subchain
	 *            object of type SubchainType
	 */
	public void addSubchain(SubchainType subchain) {
		mToolchain.getPluginOrSubchain().add(subchain);
	}

	/**
	 * This method appends an already existing object of type Toolchain to the
	 * end of this toolchain.
	 * 
	 * @param tc
	 *            the Toolchain object to be appended to this Toolchain object
	 */
	public void addToolchain(ToolchainData tc) {
		mToolchain.getPluginOrSubchain().addAll(tc.getToolchain().getPluginOrSubchain());
	}

	public ToolchainListType getToolchain() {
		return mToolchain;
	}
	
	public IToolchainStorage getStorage(){
		return mStorage;
	}
	
	public IUltimateServiceProvider getServices(){
		return mStorage;
	}
}
