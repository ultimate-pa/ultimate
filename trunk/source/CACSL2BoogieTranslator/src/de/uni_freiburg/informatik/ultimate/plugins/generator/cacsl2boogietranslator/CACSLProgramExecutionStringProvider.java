package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IPointerType;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTIdExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.ACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.result.ProgramExecutionFormatter.IProgramExecutionStringProvider;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class CACSLProgramExecutionStringProvider implements
		IProgramExecutionStringProvider<CACSLLocation, IASTExpression> {

	@Override
	public int getStartLineNumberFromStep(CACSLLocation step) {
		return step.getStartLine();
	}

	@Override
	public int getEndLineNumberFromStep(CACSLLocation step) {
		return step.getEndLine();
	}

	@Override
	public String getStringFromStep(CACSLLocation step) {
		if (step instanceof CLocation) {
			return getStringFromIASTNode(((CLocation) step).getNode());
		} else if (step instanceof ACSLLocation) {
			return ((ACSLLocation) step).getNode().toString();
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public String getStringFromTraceElement(CACSLLocation traceelement) {
		return getStringFromStep(traceelement);
	}

	@Override
	public String getStringFromExpression(IASTExpression expression) {
		return getStringFromIASTNode(expression);
	}

	private String getStringFromIASTNode(IASTNode currentStepNode) {
		String str = currentStepNode.getRawSignature();
		if (currentStepNode instanceof CASTIdExpression) {
			CASTIdExpression id = (CASTIdExpression) currentStepNode;
			if (id.getExpressionType() instanceof IPointerType) {
				str = "\\read(" + getPointerStars((IPointerType) id.getExpressionType()) + str + ")";
			} else {
				str = "\\read(" + str + ")";
			}
		}
		return str;
	}

	private String getPointerStars(IPointerType type) {
		if (type.getType() instanceof IPointerType) {
			return "*" + getPointerStars((IPointerType) type.getType());
		} else {
			return "*";
		}
	}

}