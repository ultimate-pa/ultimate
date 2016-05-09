/*
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import net.sf.javabdd.BDDFactory;

/**
 * Some BDD based simplification.
 * TODO: More detailed documentation.
 * @author Michael Steinle
 *
 */
public class SimplifyBdd {
	
	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final Logger mLogger;
	//TODO: 2016-05-09 Matthias: The following field might be be useless
	private final IFreshTermVariableConstructor mFreshTermVariableConstructor;
	
	public SimplifyBdd(IUltimateServiceProvider services, Script script,
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		super();
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mScript = script;
		mFreshTermVariableConstructor = freshTermVariableConstructor;
	}
	
	
	/**
	 * Transform input into simplified term. 
	 * @return Term which is logically equivalent to input.
	 */
	public Term transform(final Term input) {
		final BDDFactory bddfac = null;
		return input;
	}
	
	
	/**
	 * Class for transforming {@link Term}s into a BDD. 
	 *
	 */
	private class BddBuilder extends NonRecursive {
		
	}
	

}
