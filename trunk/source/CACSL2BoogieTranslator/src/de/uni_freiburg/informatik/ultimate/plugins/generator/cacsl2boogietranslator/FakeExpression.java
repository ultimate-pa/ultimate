package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.ExpansionOverlapsBoundaryException;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNodeLocation;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.parser.IToken;

/**
 * This evil class allows us to create identifier or value expressions for the
 * purpose of backtranslation without having to rebuild a complete CDT AST from
 * scratch.
 * 
 * It is more or less an evil hack into the structures of CDT, but so what...
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class FakeExpression implements IASTExpression {

	private String mName;
	private IASTNode mBackingNode;

	public FakeExpression(String name) {
		mName = name;
	}
	
	public FakeExpression(IASTNode actualNode, String name) {
		mBackingNode = actualNode;
		mName = name;
	}

	@Override
	public IASTTranslationUnit getTranslationUnit() {
		if(mBackingNode != null){
			return mBackingNode.getTranslationUnit();
		}
		return null;
	}

	@Override
	public IASTNodeLocation[] getNodeLocations() {
		if(mBackingNode != null){
			return mBackingNode.getNodeLocations();
		}
		return null;
	}

	@Override
	public IASTFileLocation getFileLocation() {
		if(mBackingNode != null){
			return mBackingNode.getFileLocation();
		}
		return null;
	}

	@Override
	public String getContainingFilename() {
		if(mBackingNode!=null){
			return mBackingNode.getContainingFilename();
		}
		return null;
	}

	@Override
	public boolean isPartOfTranslationUnitFile() {
		if(mBackingNode!=null){
			return mBackingNode.isPartOfTranslationUnitFile();
		}
		return false;
	}

	@Override
	public IASTNode getParent() {
		if(mBackingNode!=null){
			return mBackingNode.getParent();
		}
		return null;
	}

	@Override
	public IASTNode[] getChildren() {
		if(mBackingNode!=null){
			return mBackingNode.getChildren();
		}
		return null;
	}

	@Override
	public void setParent(IASTNode node) {
		if(mBackingNode!=null){
			mBackingNode.setParent(node);
		}
	}

	@Override
	public ASTNodeProperty getPropertyInParent() {
		if(mBackingNode!=null){
			return mBackingNode.getPropertyInParent();
		}
		return null;
	}

	@Override
	public void setPropertyInParent(ASTNodeProperty property) {
		if(mBackingNode!=null){
			mBackingNode.setPropertyInParent(property);
		}
	}

	@Override
	public boolean accept(ASTVisitor visitor) {
		if(mBackingNode!=null){
			return mBackingNode.accept(visitor);
		}
		return false;
	}

	@Override
	public String getRawSignature() {
		return mName;
	}

	@Override
	public boolean contains(IASTNode node) {
		if(mBackingNode!=null){
			return mBackingNode.contains(node);
		}
		return false;
	}

	@Override
	public IToken getLeadingSyntax() throws ExpansionOverlapsBoundaryException, UnsupportedOperationException {
		if(mBackingNode!=null){
			return mBackingNode.getLeadingSyntax();
		}
		return null;
	}

	@Override
	public IToken getTrailingSyntax() throws ExpansionOverlapsBoundaryException, UnsupportedOperationException {
		if(mBackingNode!=null){
			return mBackingNode.getTrailingSyntax();
		}
		return null;
	}

	@Override
	public IToken getSyntax() throws ExpansionOverlapsBoundaryException {
		if(mBackingNode!=null){
			return mBackingNode.getSyntax();
		}
		return null;
	}

	@Override
	public boolean isFrozen() {
		if(mBackingNode!=null){
			return mBackingNode.isFrozen();
		}
		return true;
	}

	@Override
	public boolean isActive() {
		if(mBackingNode!=null){
			return mBackingNode.isActive();
		}
		return false;
	}

	@Override
	public IASTNode getOriginalNode() {
		if(mBackingNode!=null){
			return mBackingNode.getOriginalNode();
		}
		return null;
	}

	@Override
	public IType getExpressionType() {
		return null;
	}

	@Override
	public boolean isLValue() {
		return false;
	}

	@Override
	public ValueCategory getValueCategory() {
		return null;
	}

	@Override
	public IASTExpression copy() {
		return null;
	}

	@Override
	public IASTExpression copy(CopyStyle style) {
		return null;
	}

	@Override
	public String toString() {
		return mName;
	}

}
