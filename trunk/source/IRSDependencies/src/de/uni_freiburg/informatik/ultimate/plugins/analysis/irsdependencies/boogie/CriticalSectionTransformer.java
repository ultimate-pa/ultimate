/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class CriticalSectionTransformer extends BoogieTransformer {
	
	protected SymbolTable mSymbolTable;
	private final ILogger mLogger;
	
	public CriticalSectionTransformer(SymbolTable symbolTable, ILogger logger) {
		mSymbolTable = symbolTable;
		mLogger = logger;
	}

	public boolean process(IElement root)
	{
		if (root instanceof WrapperNode) {
			final Unit unit = (Unit) ((WrapperNode) root).getBacking();
			final Declaration[] declarations = unit.getDeclarations();

			for (final Declaration decl : declarations) {
				processDeclaration(decl);
			}
			return false;
		}
		else {
			return true;
		}
	}
	
	@Override
	protected Declaration processDeclaration(Declaration decl) {
		mLogger.debug(decl);
		return super.processDeclaration(decl);
	}
	
	@Override
	protected Body processBody(Body body) {
		mLogger.debug(body);
		return super.processBody(body);
	}
	
	@Override
	protected Statement processStatement(Statement statement) {
		mLogger.debug(statement);
		return super.processStatement(statement);
	}

}
