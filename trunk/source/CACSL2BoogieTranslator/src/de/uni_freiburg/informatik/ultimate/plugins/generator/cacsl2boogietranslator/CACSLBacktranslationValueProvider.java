/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IPointerType;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIdExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class CACSLBacktranslationValueProvider implements IBacktranslationValueProvider<CACSLLocation, IASTExpression> {

	@Override
	public int getStartLineNumberFromStep(final CACSLLocation step) {
		return step.getStartLine();
	}

	@Override
	public int getEndLineNumberFromStep(final CACSLLocation step) {
		return step.getEndLine();
	}

	@Override
	public String getStringFromStep(final CACSLLocation step) {
		if (step instanceof CLocation) {
			return getStringFromIASTNode(((CLocation) step).getNode());
		} else if (step instanceof ACSLLocation) {
			return ((ACSLLocation) step).getNode().toString();
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public String getStringFromTraceElement(final CACSLLocation traceelement) {
		return getStringFromStep(traceelement);
	}

	@Override
	public String getStringFromExpression(final IASTExpression expression) {
		return getStringFromIASTNode(expression);
	}

	private String getStringFromIASTNode(final IASTNode currentStepNode) {
		String str = currentStepNode.getRawSignature();
		if (currentStepNode instanceof CASTIdExpression) {
			final CASTIdExpression id = (CASTIdExpression) currentStepNode;
			if (id.getExpressionType() instanceof IPointerType) {
				str = "\\read(" + getPointerStars((IPointerType) id.getExpressionType()) + str + ")";
			} else {
				str = "\\read(" + str + ")";
			}
		}
		return str;
	}

	private String getPointerStars(final IPointerType type) {
		if (type.getType() instanceof IPointerType) {
			return "*" + getPointerStars((IPointerType) type.getType());
		}
		return "*";
	}

	@Override
	public String getFileNameFromStep(final CACSLLocation step) {
		return step.getFileName();
	}

	@Override
	public String getOriginFileNameFromStep(final CACSLLocation step) {
		return step.getFileName();
	}

}
