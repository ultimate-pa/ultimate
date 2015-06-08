package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.ast.SpaceExModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ObjectFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExParserPreferenceInitializer;

/**
 * @author Marius Greitschus
 *
 */
public class SpaceExParser implements ISource {

    private final String[] mFileTypes;
    private List<String> mFileNames;
    private IUltimateServiceProvider mServices;
    private Logger mLogger;

    /**
     * Constructor of the SpaceEx Parser plugin.
     */
    public SpaceExParser() {
        mFileTypes = new String[] { "xml", };
        mFileNames = new ArrayList<String>();
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
        // Auto-generated method stub
    }

    @Override
    public void finish() {
        // Auto-generated method stub
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

        boolean knownExtension = false;

        for (String s : getFileTypes()) {
            if (file.getName().endsWith(s)) {
                knownExtension = true;
                break;
            }
        }

        if (!knownExtension) {
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
    	mFileNames.add(file.getName());
    	
        final FileInputStream fis = new FileInputStream(file);

        final JAXBContext jaxContext = JAXBContext.newInstance(ObjectFactory.class);

        final Unmarshaller unmarshaller = jaxContext.createUnmarshaller();

        final Sspaceex spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);

        final Marshaller marshaller = jaxContext.createMarshaller();

        marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE);

        final StringWriter streamWriter = new StringWriter();

        marshaller.marshal(spaceEx, streamWriter);

        mLogger.info(streamWriter.toString());

        fis.close();

        return new SpaceExModel();
    }

    @Override
    public String[] getFileTypes() {
        return mFileTypes;
    }

    @Override
    public GraphType getOutputDefinition() {
    	try {
	        return new GraphType(Activator.PLUGIN_ID, "SpaceExParser", mFileNames);
        } catch (Exception e) {
	        // TODO Auto-generated catch block
	        e.printStackTrace();
        }
    	return null;
    }

    @Override
    public void setPreludeFile(File prelude) {
        // TODO Auto-generated method stub

    }

}
