//package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler;
//
//import java.util.List;
//
//import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
//
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.FunctionHandler;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
//import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
//
///**
// * @author Markus Lindenmann
// * @date 21.10.2012
// */
//public class SVCompFunctionHandler extends FunctionHandler {
//    @Override
//    public Result handleFunctionDeclaration(Dispatcher main,
//            List<ACSLNode> contract, IASTSimpleDeclaration node) {
//        Result r = null;
//        try {
//            r = super.handleFunctionDeclaration(main, contract, node);
//        } catch (ClassCastException cce) {
//            r = new ResultSkip();
//        }
//        assert r != null;
//        return r;
//    }
//}
