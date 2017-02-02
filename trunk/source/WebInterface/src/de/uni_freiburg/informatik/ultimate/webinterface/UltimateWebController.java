package de.uni_freiburg.informatik.ultimate.webinterface;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBException;

import org.json.JSONObject;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.external.ExternalUltimateCore;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class UltimateWebController implements IController<RunDefinition> {

	private final File mSettingsFile;
	private final File mInputFile;
	private final File mToolchainFile;
	private final long mDeadline;

	private IUltimateServiceProvider mCurrentServices;
	private final ExternalUltimateCore mExternalUltimateCore;
	private ICore<RunDefinition> mCore;

	public UltimateWebController(final File settings, final File input, final File toolchain, final long deadline) {
		mExternalUltimateCore = new ExternalUltimateCore(this);
		mSettingsFile = settings;
		mInputFile = input;
		mToolchainFile = toolchain;
		mDeadline = deadline;
	}

	public JSONObject runUltimate(final JSONObject json) {
		try {
			mExternalUltimateCore.runUltimate();
			UltimateResultProcessor.processUltimateResults(mCurrentServices, json);
		} catch (final Throwable e) {
			e.printStackTrace();
		} finally {
			mExternalUltimateCore.complete();
		}
		return json;
	}

	@Override
	public int init(final ICore<RunDefinition> core) {
		// TODO Use own logging service to prefix each ultimate log line with
		// the session id
		// TODO: check what the whole settings thing means in parallel contexts
		// clear old preferences
		mCore = core;
		core.resetPreferences();
		return mExternalUltimateCore.init(core, mSettingsFile, mDeadline, new File[] { mInputFile }).getCode();
	}

	@Override
	public IToolchainData<RunDefinition> selectTools(final List<ITool> tools) {
		try {
			final IToolchainData<RunDefinition> tc = mCore.createToolchainData(mToolchainFile.getAbsolutePath());
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
	public ISource selectParser(final Collection<ISource> parser) {
		return null;
	}

	@Override
	public List<String> selectModel(final List<String> modelNames) {
		return null;
	}

	@Override
	public void displayToolchainResults(final IToolchainData<RunDefinition> toolchain,
			final Map<String, List<IResult>> results) {
		// TODO Auto-generated method stub

	}

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		// TODO Auto-generated method stub

	}
}
