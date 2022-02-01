/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE LTL2Aut plug-in.
 *
 * The ULTIMATE LTL2Aut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LTL2Aut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LTL2Aut plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LTL2Aut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LTL2Aut plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 */
public class LTL2aut implements IGenerator, ISource {

	protected List<String> mFileNames;
	private boolean mProcess;
	private boolean mSkip;
	private int mUseful;

	private LTL2autObserver mObserver;
	private IUltimateServiceProvider mServices;
	private final String[] mFileTypes;
	private ILogger mLogger;

	public LTL2aut() {
		mFileNames = new ArrayList<>();
		mFileTypes = new String[] { "ltl" };
	}

	@Override
	public void init() {
		mProcess = false;
		mUseful = 0;

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
	public ModelType getOutputDefinition() {
		final List<String> filenames = new ArrayList<>();
		filenames.add("Hardcoded");

		return new ModelType(Activator.PLUGIN_ID, ModelType.Type.AST, filenames);
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		if (mSkip) {
			return ModelQuery.LAST;
		}
		return ModelQuery.ALL;
	}

	@Override
	public List<String> getDesiredToolIds() {
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		switch (graphType.getCreator()) {
		case "de.uni_freiburg.informatik.ultimate.boogie.parser":
		case "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator":
			mProcess = true;
			mUseful++;
			break;
		default:
			mProcess = false;
			break;
		}
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new LTL2autObserver(mServices);
		final ArrayList<IObserver> observers = new ArrayList<>();
		if (mProcess && !mSkip) {
			observers.add(mObserver);
		}
		return observers;
	}

	@Override
	public IElement getModel() {
		return mObserver.getNWAContainer();
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@SuppressWarnings("rawtypes")
	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		final Collection<CounterExampleResult> cex =
				ResultUtil.filterResults(services.getResultService().getResults(), CounterExampleResult.class);
		mSkip = !cex.isEmpty();
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_NAME);
	}

	@Override
	public void finish() {
		if (!mSkip && mUseful == 0) {
			throw new IllegalStateException("Was used in a toolchain were it did nothing");
		}
		if (mSkip) {
			mServices.getLoggingService().getLogger(getPluginID())
					.info("Another plugin discovered errors, skipping...");
		}
	}

	@Override
	public File[] parseable(final File[] files) {
		final List<File> rtrList = Arrays.stream(files).filter(this::parseable).collect(Collectors.toList());
		return rtrList.toArray(new File[rtrList.size()]);
	}

	private boolean parseable(final File file) {
		for (final String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		if (files.length == 1) {
			return parseAST(files[0]);
		}
		throw new UnsupportedOperationException("Cannot parse more than one file");
	}

	private IElement parseAST(final File file) throws Exception {
		mUseful++;
		final LTLFileParser ltlFileParser = new LTLFileParser(mLogger);
		return ltlFileParser.parse(file);
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}
}
