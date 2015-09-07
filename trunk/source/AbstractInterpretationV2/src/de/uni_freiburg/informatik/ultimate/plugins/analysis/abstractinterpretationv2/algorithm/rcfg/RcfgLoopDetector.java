/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class RcfgLoopDetector implements ILoopDetector<CodeBlock> {

	private HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> mLoops;

	public RcfgLoopDetector(RCFGLoopDetector loopDetector) {
		mLoops = loopDetector.getResult();
	}

	@Override
	public CodeBlock getLoopExit(CodeBlock transition) {
		assert transition != null;
		final RCFGNode source = transition.getSource();
		final HashMap<RCFGEdge, RCFGEdge> loops = mLoops.get(source);
		if (loops == null) {
			return null;
		}
		final RCFGEdge exit = loops.get(transition);
		if (exit instanceof CodeBlock) {
			return (CodeBlock) exit;
		}
		assert exit == null;
		return null;
	}

}
