package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorPragmaStatement;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PreprocessorHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;

public class SvComp14PreprocessorHandler extends PreprocessorHandler {

	@Override
	public Result visit(Dispatcher main, IASTPreprocessorIncludeStatement node) {
		// Ignore #include in our sv-comp mode
		return new ResultSkip();
	}

	@Override
	public Result visit(Dispatcher main, IASTPreprocessorPragmaStatement node) {
		// TODO Auto-generated method stub
		//return super.visit(main, node);
		return new ResultSkip();
	}
	

}
