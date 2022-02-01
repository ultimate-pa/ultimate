/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

/***
 * Represents a unique Boogie variable based on its declaration.  
 * 
 * @author dietsch
 */
public class ScopedBoogieVar {

	private final VariableDeclaration mDeclaration;
	private final String mIdentifier;
	private final DeclarationInformation mDeclarationInformation;
	private final IProgramVar mBoogieVar;

	public ScopedBoogieVar(String identifier, VariableDeclaration declaration,
			DeclarationInformation declarationInformation, IProgramVar var) {
		mIdentifier = identifier;
		mDeclaration = declaration;
		mDeclarationInformation = declarationInformation;
		mBoogieVar = var;
	}

	public VariableDeclaration getDeclaration() {
		return mDeclaration;
	}

	public String getIdentifier() {
		return mIdentifier;
	}

	public DeclarationInformation getDeclarationInformation() {
		return mDeclarationInformation;
	}

	public IProgramVar getBoogieVar() {
		return mBoogieVar;
	}

	@Override
	public String toString() {
		return BoogiePrettyPrinter.print(getDeclaration());
	}

}
