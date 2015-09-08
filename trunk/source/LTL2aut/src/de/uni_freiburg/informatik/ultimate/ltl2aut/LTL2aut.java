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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;

public class LTL2aut implements IGenerator {

	protected List<String> mFileNames;
	private boolean mProcess;
	private boolean mSkip;
	private int mUseful;

	private LTL2autObserver mObserver;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;

	public LTL2aut() {
		mFileNames = new ArrayList<String>();
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
	public GraphType getOutputDefinition() {
		List<String> filenames = new ArrayList<String>();
		filenames.add("Hardcoded");

		return new GraphType(Activator.PLUGIN_ID, GraphType.Type.AST, filenames);
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		if (mSkip) {
			return QueryKeyword.LAST;
		}
		return QueryKeyword.ALL;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
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
		mObserver = new LTL2autObserver(mServices, mStorage);
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
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
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		mStorage = storage;
	}

	@SuppressWarnings("rawtypes")
	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		Collection<CounterExampleResult> cex = CoreUtil.filterResults(services.getResultService().getResults(),
				CounterExampleResult.class);
		mSkip = !cex.isEmpty();
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

}
