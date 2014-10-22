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

	public FakeExpression() {

	}

	public FakeExpression(String name) {
		mName = name;
	}

	private String mName;

	public void setNameOrValue(String name) {
		mName = name;
	}

	@Override
	public IASTTranslationUnit getTranslationUnit() {
		return null;
	}

	@Override
	public IASTNodeLocation[] getNodeLocations() {
		return null;
	}

	@Override
	public IASTFileLocation getFileLocation() {
		return null;
	}

	@Override
	public String getContainingFilename() {
		return null;
	}

	@Override
	public boolean isPartOfTranslationUnitFile() {
		return false;
	}

	@Override
	public IASTNode getParent() {
		return null;
	}

	@Override
	public IASTNode[] getChildren() {
		return null;
	}

	@Override
	public void setParent(IASTNode node) {

	}

	@Override
	public ASTNodeProperty getPropertyInParent() {
		return null;
	}

	@Override
	public void setPropertyInParent(ASTNodeProperty property) {

	}

	@Override
	public boolean accept(ASTVisitor visitor) {
		return false;
	}

	@Override
	public String getRawSignature() {
		return mName;
	}

	@Override
	public boolean contains(IASTNode node) {
		return false;
	}

	@Override
	public IToken getLeadingSyntax() throws ExpansionOverlapsBoundaryException, UnsupportedOperationException {
		return null;
	}

	@Override
	public IToken getTrailingSyntax() throws ExpansionOverlapsBoundaryException, UnsupportedOperationException {
		return null;
	}

	@Override
	public IToken getSyntax() throws ExpansionOverlapsBoundaryException {
		return null;
	}

	@Override
	public boolean isFrozen() {
		return false;
	}

	@Override
	public boolean isActive() {
		return false;
	}

	@Override
	public IASTNode getOriginalNode() {
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
