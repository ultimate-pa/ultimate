/*
 * Copyright (C) 2017 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 * 
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;

/**
 * Class that handles conversion of Hybrid Models/Systems/Automata to an ICFG
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridIcfgGenerator {
	
	List<HybridEdge> mIcfgEdges;
	List<HybridLocation> mIcfgLocations;
	
	public HybridIcfgGenerator() {
		mIcfgEdges = new ArrayList<>();
		mIcfgLocations = new ArrayList<>();
		
	}
	
	public void modelToIcfg(HybridModel model) {
		
	}
	
	private void automataToIcfg(HybridAutomaton automata) {
		
	}
	
	private void systemToIcfg(HybridSystem system) {
		
	}
	
	/*
	 * variable methods
	 */
	
	private void variableToIcfg() {
		
	}
	
	/*
	 * Transition methods
	 */
	
	private void transitionToIcfg() {
		
	}
	
	private void guardToIcfg() {
		
	}
	
	private void updateToIcfg() {
		
	}
	
	/*
	 * Location methods
	 */
	private void locationToIcfg() {
		
	}
	
	private void flowToIcfg() {
		
	}
	
	private void invariantToIcfg() {
		
	}
}
