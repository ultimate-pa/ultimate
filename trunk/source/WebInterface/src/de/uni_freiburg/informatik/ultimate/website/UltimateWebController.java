package de.uni_freiburg.informatik.ultimate.website;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.json.JSONObject;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.external.ExternalUltimateCore;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainListType;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class UltimateWebController implements IController<ToolchainListType> {

	private final File mSettingsFile;
	private final File mInputFile;
	private final File mToolchainFile;
	private final long mDeadline;

	private IUltimateServiceProvider mCurrentServices;
	private final ExternalUltimateCore mExternalUltimateCore;
	private ICore<ToolchainListType> mCore;

	public UltimateWebController(File settings, File input, File toolchain, long deadline) {
		mExternalUltimateCore = new ExternalUltimateCore(this);
		mSettingsFile = settings;
		mInputFile = input;
		mToolchainFile = toolchain;
		mDeadline = deadline;
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
	public int init(ICore<ToolchainListType> core, ILoggingService loggingService) {
		// TODO Use own logging service to prefix each ultimate log line with
		// the session id
		// TODO: check what the whole settings thing means in parallel contexts
		// clear old preferences
		mCore = core;
		core.resetPreferences();
		return mExternalUltimateCore.init(core, loggingService, mSettingsFile, mDeadline, new File[] { mInputFile })
				.getCode();
	}

	@Override
	public IToolchainData<ToolchainListType> selectTools(List<ITool> tools) {
		try {
			final IToolchainData<ToolchainListType> tc = mCore.createToolchainData(mToolchainFile.getAbsolutePath());
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
	public IPreferenceInitializer getPreferences() {
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
