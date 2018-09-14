package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.text.ParseException;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;

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
}