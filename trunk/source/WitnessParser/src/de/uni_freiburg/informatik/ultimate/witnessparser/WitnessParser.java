package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.GraphType.Type;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class WitnessParser implements ISource {

	private static final String[] sFileTypes = new String[] { "graphml" };
	private IUltimateServiceProvider mServices;
	private String mFilename;

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void init() {

	}

	@Override
	public void finish() {

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
		return null;
	}

	@Override
	public boolean parseable(File[] files) {
		if (files != null && files.length == 1) {
			return parseable(files[0]);
		}
		return false;
	}

	@Override
	public boolean parseable(File file) {
		if (file != null && file.exists() && file.isFile()) {
			for (String suffix : getFileTypes()) {
				if (file.getName().endsWith(suffix)) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		if (files == null || files.length != 1) {
			throw new UnsupportedOperationException("We currently do not support multiple witnesses");
		}
		return parseAST(files[0]);
	}

	@Override
	public IElement parseAST(File file) throws Exception {
		mFilename = file.getAbsolutePath();
		return new WitnessAutomatonConstructor(mServices).constructWitnessAutomaton(file);
	}

	@Override
	public String[] getFileTypes() {
		return sFileTypes;
	}

	@Override
	public GraphType getOutputDefinition() {
		return new GraphType(getPluginID(), Type.OTHER, Collections.singleton(mFilename));
	}

	@Override
	public void setPreludeFile(File prelude) {

	}

}
