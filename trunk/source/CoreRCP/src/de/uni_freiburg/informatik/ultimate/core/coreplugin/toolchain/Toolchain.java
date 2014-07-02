package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.HashMap;
import java.util.Map;

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

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;

/**
 * This implements the datastructure representing a Ultimate toolchain.
 * It can be used for constructing a Ultimate toolchain manually or from
 * an XML specification file.
 * 
 * @author Bj�rn Buchhold, Christian Simon
 *
 */
public class Toolchain {

	    private ObjectFactory mObjectFactory;
	    private ToolchainListType mToolchain;
	    private Map<String, IStorable> mToolchainStorage;

	    /**
	     * This constructor creates an empty toolchain.
	     */
	    public Toolchain(){
	        this.mObjectFactory = new ObjectFactory();
	        this.mToolchain = mObjectFactory.createToolchainListType();
	        this.mToolchainStorage = new HashMap<String, IStorable>();
	    }
	    
	    private boolean isReady(Bundle bundle){
	    	return bundle != null && (bundle.getState() & (Bundle.RESOLVED | Bundle.STARTING | Bundle.ACTIVE | Bundle.STOPPING)) != 0;
	    }
	    
	    /**
	     * This constructor creates a toolchain from an XML file.
	     * 
	     * @param xmlfile an xml file compliant with toolchain.xsd 
	     * @throws JAXBException
	     * @throws FileNotFoundException
	     * @throws SAXException 
	     * @throws MalformedURLException 
	     */
	    @SuppressWarnings({ "unchecked" })
		public Toolchain(String xmlfile) throws JAXBException, FileNotFoundException, SAXException {
	    	this.mObjectFactory = new ObjectFactory(); 
	    	JAXBContext jc = JAXBContext.newInstance("de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain" );

	    	// all this effort just for validating the input XML file...
	    	Bundle bundle = Platform.getBundle(Activator.s_PLUGIN_ID);
	    	
	        if (!isReady(bundle)) {
				System.err.println("Bundle not ready");
			}

	        URL fullPathString = FileLocator.find(bundle, new Path("src/de/uni_freiburg/informatik/ultimate/core/coreplugin/toolchain/toolchain.xsd"),null);
	        if (fullPathString == null) {
	            try {
	                fullPathString = new URL("src/de/uni_freiburg/informatik/ultimate/core/coreplugin/toolchain/toolchain.xsd");
	            } catch (MalformedURLException e) {
	                e.printStackTrace();
	            }
	        }
	        
			Unmarshaller u = jc.createUnmarshaller();
			u.setSchema(SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI).newSchema(fullPathString));

			JAXBElement<ToolchainListType> doc = 
				(JAXBElement<ToolchainListType>) u.unmarshal(new FileInputStream(xmlfile));
			
			this.mToolchain = doc.getValue();
			this.mToolchainStorage = new HashMap<String, IStorable>();
	    }

	    
	    
	    /**
	     * This method marshals a toolchain into an xml file.
	     * 
	     * @param xmlfile
	     * @throws JAXBException
	     * @throws FileNotFoundException
	     */
	    public void writeToFile(String xmlfile) throws JAXBException, FileNotFoundException {
	    	 JAXBContext jc = JAXBContext.newInstance("de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain" );
	    	 JAXBElement<ToolchainListType> newdoc =
	             mObjectFactory.createToolchain(this.mToolchain);
	         Marshaller m = jc.createMarshaller();
	         m.marshal(newdoc, new FileOutputStream(xmlfile) );
	    }
	   
	    /**
	     * This method adds a Plugin to the Toolchain. The plugin
	     * object must have been previously instantiated using
	     * ObjectFactory.
	     * 
	     * @param plugin object of type PluginType
	     */
	    public void addPlugin(PluginType plugin) {
	    	this.mToolchain.getPluginOrSubchain().add(plugin);
	    }
	    

	    /**
	     * This method adds a plugin / tool to the toolchain by creating
	     * a new plugin object from a plugin name first.
	     * 
	     * @param name of the desired plugin
	     */
	    public void addPlugin(String name) {
	    	PluginType foo = new PluginType();
	    	foo.setId(name);
	    	this.mToolchain.getPluginOrSubchain().add(foo);
	    }
	    
	    /**
	     * This method adds a Subchain to the Toolchain. The subchain
	     * object must have been previously instantiated using
	     * ObjectFactory.
	     * 
	     * @param subchain object of type SubchainType
	     */
	    public void addSubchain(SubchainType subchain) {
	    	this.mToolchain.getPluginOrSubchain().add(subchain);
	    }
	    
	    /**
	     * This method appends an already existing object of 
	     * type Toolchain to the end of this toolchain.
	     * 
	     * @param tc the Toolchain object to be appended to this Toolchain object
	     */
	    public void addToolchain(Toolchain tc) {
	    	this.mToolchain.getPluginOrSubchain().addAll(tc.getToolchain().getPluginOrSubchain());
	    }
	    
	    public ToolchainListType getToolchain() {
	    	return this.mToolchain;
	    }

		public IStorable getStoredObject(String key){
			return this.mToolchainStorage.get(key);
		}
		
		public void putIntoStorage(String key, IStorable value){
			this.mToolchainStorage.put(key, value);
		}
		
		/**
		 * This method clears the toolchain storage space by
		 * iterating over the map and destroying every object
		 * of type IStorable contained. Possible exceptions raise
		 * will be caught and ignored.
		 */
		public void clearStore(){
			for (IStorable storable : this.mToolchainStorage.values()) {
				// all exceptions shall be caught and ignored
				try {
					storable.destroy();
				} catch (Exception e) {
					UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID).error("An error occurred while trying to free Storable "+storable.toString());
				}
			}
			this.mToolchainStorage.clear();
		}
	    
	}

