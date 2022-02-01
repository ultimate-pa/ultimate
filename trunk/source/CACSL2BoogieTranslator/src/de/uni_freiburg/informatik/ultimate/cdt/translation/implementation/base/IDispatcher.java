/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.text.ParseException;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;

import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CHandlerTranslationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

public interface IDispatcher {

	CHandlerTranslationResult dispatch(final List<DecoratedUnit> nodes);

	/**
	 * Dispatch a given C node to a specific handler.
	 *
	 * @param node
	 *            the node to dispatch
	 * @return the result for the given node
	 */
	Result dispatch(IASTNode node);

	/**
	 * Dispatch a given C node to a specific handler.
	 *
	 * @param node
	 *            the node to dispatch.
	 * @return the resulting translation.
	 */
	Result dispatch(IASTPreprocessorStatement node);

	/**
	 * Dispatch a given ACSL node to the specific handler.
	 *
	 * @param node
	 *            the node to dispatch
	 * @param cHook
	 *            the C AST node where this ACSL node has scope access
	 * @return the result for the given node
	 */
	Result dispatch(ACSLNode node, IASTNode cHook);

	/**
	 * Dispatch a given ACSL node to the specific handler. Shortcut for methods where the hook does not change.
	 *
	 * @param node
	 *            the node to dispatch
	 * @param cHook
	 *            the C AST node where this ACSL node has scope access
	 * @return the result for the given node
	 */
	Result dispatch(ACSLNode node);

	IASTNode getAcslHook();

	NextACSL nextACSLStatement() throws ParseException;

	LoopInvariantSpecification fetchInvariantAtLoop(final IASTNode node);
}