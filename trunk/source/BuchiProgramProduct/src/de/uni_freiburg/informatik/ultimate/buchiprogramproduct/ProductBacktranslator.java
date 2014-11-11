package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class ProductBacktranslator extends DefaultTranslator<RCFGEdge,CodeBlock, Expression, Expression> {

	public ProductBacktranslator(Class<RCFGEdge> sourceTraceElementType, Class<CodeBlock> targetTraceElementType,
			Class<Expression> sourceExpressionType, Class<Expression> targetExpressionType) {
		super(sourceTraceElementType, targetTraceElementType, sourceExpressionType, targetExpressionType);
	}

	@Override
	public IProgramExecution<CodeBlock, Expression> translateProgramExecution(
			IProgramExecution<RCFGEdge, Expression> programExecution) {
		return super.translateProgramExecution(programExecution);
	}
	

}
