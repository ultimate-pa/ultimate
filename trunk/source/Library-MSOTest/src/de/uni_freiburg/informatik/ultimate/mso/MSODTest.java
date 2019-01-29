/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import org.junit.Before;
import org.junit.Rule;
import org.junit.rules.ExpectedException;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public abstract class MSODTest {

	protected IUltimateServiceProvider mServiceProvider;
	protected AutomataLibraryServices mServices;
	protected Script mScript;
	protected ILogger mLogger;

	protected Term x;
	protected Term y;
	protected MSODAlphabetSymbol x0;
	protected MSODAlphabetSymbol x1;
	protected MSODAlphabetSymbol xy00;
	protected MSODAlphabetSymbol xy01;
	protected MSODAlphabetSymbol xy10;
	protected MSODAlphabetSymbol xy11;

	@Rule
	public final ExpectedException mNoException = ExpectedException.none();

	@Before
	public void setUp() {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mServices = new AutomataLibraryServices(mServiceProvider);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = mServiceProvider.getLoggingService().getLogger("lol");

		mScript.setLogic(Logics.ALL);
		mScript.declareSort("SetOfInt", 0);

		x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		y = mScript.variable("y", MoNatDiffUtils.getSetOfIntSort(mScript));

		x0 = new MSODAlphabetSymbol(x, false);
		x1 = new MSODAlphabetSymbol(x, true);
		xy00 = new MSODAlphabetSymbol(x, y, false, false);
		xy10 = new MSODAlphabetSymbol(x, y, true, false);
		xy01 = new MSODAlphabetSymbol(x, y, false, true);
		xy11 = new MSODAlphabetSymbol(x, y, true, true);
	}
}
