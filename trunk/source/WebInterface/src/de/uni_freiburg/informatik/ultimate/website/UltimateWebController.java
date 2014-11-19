package de.uni_freiburg.informatik.ultimate.website;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.json.JSONObject;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.controllers.ExternalUltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class UltimateWebController implements IController {

	private final File mSettingsFile;
	private final File mInputFile;
	private final File mToolchainFile;

	private IUltimateServiceProvider mCurrentServices;
	private final ExternalUltimateCore mExternalUltimateCore;

	public UltimateWebController(File settings, File input, File toolchain) {
		mExternalUltimateCore = new ExternalUltimateCore(this);
		mSettingsFile = settings;
		mInputFile = input;
		mToolchainFile = toolchain;
	}

	public JSONObject runUltimate(JSONObject json) {
		try {
			mExternalUltimateCore.runUltimate();
			UltimateResultProcessor.processUltimateResults(mCurrentServices, json);
		} catch (Throwable e) {
			e.printStackTrace();
		} finally {
			mExternalUltimateCore.complete();
		}
		return json;
	}

	@Override
	public int init(ICore core, ILoggingService loggingService) {
		return mExternalUltimateCore.init(core, loggingService, mSettingsFile, 0, mInputFile, null);
	}

	@Override
	public ToolchainData selectTools(List<ITool> tools) {
		try {
			ToolchainData tc = new ToolchainData(mToolchainFile.getAbsolutePath());
			mCurrentServices = tc.getServices();
			return tc;
		} catch (FileNotFoundException | JAXBException | SAXException e) {
			e.printStackTrace();
			return null;
		}
	}

	@Override
	public String getPluginName() {
		return getPluginID();
	}

	@Override
	public String getPluginID() {
		return "Webinterface";
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public ISource selectParser(Collection<ISource> parser) {
		return null;
	}

	@Override
	public List<String> selectModel(List<String> modelNames) {
		return null;
	}

	@Override
	public void displayToolchainResultProgramIncorrect() {

	}

	@Override
	public void displayToolchainResultProgramCorrect() {

	}

	@Override
	public void displayToolchainResultProgramUnknown(String description) {

	}

	@Override
	public void displayException(String description, Throwable ex) {

	}

}
