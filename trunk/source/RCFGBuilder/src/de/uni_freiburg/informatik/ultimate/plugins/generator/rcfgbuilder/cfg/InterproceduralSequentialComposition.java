/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;

public class InterproceduralSequentialComposition extends SequentialComposition {

	private static final long serialVersionUID = -1637790156358220366L;

	InterproceduralSequentialComposition(int serialNumber, ProgramPoint source,
			ProgramPoint target, Boogie2SMT boogie2smt, 
			ModifiableGlobalVariableManager modGlobVarManager, 
			boolean simplify, boolean extPqe, List<CodeBlock> codeBlocks, Logger logger, IUltimateServiceProvider services) {
		super(serialNumber, source, target, boogie2smt, modGlobVarManager, simplify, extPqe, services, codeBlocks);
	}

	@Override
	protected void checkNumberOfCallsAndReturns(int numberCalls, int  numberReturns) {
		if(numberCalls <= numberReturns) {
			throw new IllegalArgumentException("more calls and returns required");
		}
	}
	
	
	
}
