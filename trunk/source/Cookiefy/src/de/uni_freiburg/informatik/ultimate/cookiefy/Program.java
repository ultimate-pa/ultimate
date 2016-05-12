/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jeremi Dzienian
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * 
 * This file is part of the ULTIMATE Cookiefy plug-in.
 * 
 * The ULTIMATE Cookiefy plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Cookiefy plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Cookiefy plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Cookiefy plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Cookiefy plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;

/**
 * Helper class holding preprocessed input program information
 * @author Jeremi
 * @author Vincent
 *
 */
public class Program {
	private final ILogger mLogger;
	private Unit m_Unit;
	
	public Map<String, Procedure> Procedures;
	public List<VariableDeclaration> Globals;
	public List<TypeDeclaration> Types;

	/**
	 * Constructs a new program
	 * @param logger 
	 */
	public Program(ILogger logger) {
		mLogger = logger;
		Procedures = new LinkedHashMap<String, Procedure>();
		Globals = new LinkedList<VariableDeclaration>();
		Types = new LinkedList<TypeDeclaration>();
		
	}
	
	/**
	 * Constructs a program out of a unit
	 * @param unit
	 * @param logger 
	 */
	public Program(Unit unit, ILogger logger) {
		this(logger);
		this.m_Unit = unit;

		for (Declaration decl : unit.getDeclarations()) {
			if (decl instanceof Procedure) {
				Procedure p = (Procedure)decl;
				Procedures.put(p.getIdentifier(), p);
			} else 
			if (decl instanceof VariableDeclaration) {
				Globals.add((VariableDeclaration)decl);
			} else {
				mLogger.warn(
					String.format("Cookiefy does not support this AST element: ", decl.getClass().toString()));
			}
		}
	}
	
	/**
	 * Adds a procedure into the program
	 * @param p
	 */
	public void addProcedure(Procedure p) {
		Procedures.put(p.getIdentifier(), p);
	}
	
	/**
	 * Adds multiple procedures into the program
	 * @param procedures
	 */
	public void addProcedures(Iterable<Procedure> procedures) {
		for (Procedure p : procedures) {
			Procedures.put(p.getIdentifier(), p);
		}
	}
	
	/**
	 * converts this program into a unit
	 * @return
	 */
	public Unit toUnit() {
		List<Declaration> decls = new ArrayList<Declaration>();
		
		for (TypeDeclaration var : Types) {
			decls.add(var);
		}
		
		for (VariableDeclaration var : Globals) {
			decls.add(var);
		}
		
		for (Procedure p : Procedures.values()) {
			decls.add(p);
		}
		
		return new Unit(LocationProvider.getLocation(),decls.toArray(new Declaration[decls.size()]));
	}
}
