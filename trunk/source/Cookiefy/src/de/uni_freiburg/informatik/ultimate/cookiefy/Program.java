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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Helper class holding preprocessed input program information
 *
 * @author Jeremi
 * @author Vincent
 *
 */
public class Program {
	private final ILogger mLogger;

	public Map<String, Procedure> mProcedures;
	public List<VariableDeclaration> mGlobals;
	public List<TypeDeclaration> mTypes;

	/**
	 * Constructs a new program
	 *
	 * @param logger
	 */
	public Program(final ILogger logger) {
		mLogger = logger;
		mProcedures = new LinkedHashMap<>();
		mGlobals = new LinkedList<>();
		mTypes = new LinkedList<>();

	}

	/**
	 * Constructs a program out of a unit
	 *
	 * @param unit
	 * @param logger
	 */
	public Program(final Unit unit, final ILogger logger) {
		this(logger);

		for (final Declaration decl : unit.getDeclarations()) {
			if (decl instanceof Procedure) {
				final Procedure p = (Procedure) decl;
				mProcedures.put(p.getIdentifier(), p);
			} else if (decl instanceof VariableDeclaration) {
				mGlobals.add((VariableDeclaration) decl);
			} else {
				mLogger.warn(String.format("Cookiefy does not support this AST element: ", decl.getClass().toString()));
			}
		}
	}

	/**
	 * Adds a procedure into the program
	 *
	 * @param p
	 */
	public void addProcedure(final Procedure p) {
		mProcedures.put(p.getIdentifier(), p);
	}

	/**
	 * Adds multiple procedures into the program
	 *
	 * @param procedures
	 */
	public void addProcedures(final Iterable<Procedure> procedures) {
		for (final Procedure p : procedures) {
			mProcedures.put(p.getIdentifier(), p);
		}
	}

	/**
	 * converts this program into a unit
	 *
	 * @return
	 */
	public Unit toUnit() {
		final List<Declaration> decls = new ArrayList<>();

		for (final TypeDeclaration var : mTypes) {
			decls.add(var);
		}

		for (final VariableDeclaration var : mGlobals) {
			decls.add(var);
		}

		for (final Procedure p : mProcedures.values()) {
			decls.add(p);
		}

		return new Unit(LocationProvider.getLocation(), decls.toArray(new Declaration[decls.size()]));
	}
}
