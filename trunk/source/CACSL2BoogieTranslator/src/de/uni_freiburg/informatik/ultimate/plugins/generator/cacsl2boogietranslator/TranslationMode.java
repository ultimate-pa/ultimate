/**
 * Enum holding the different translation modes available.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

/**
 * @author Markus Lindenmann
 * @date 11.06.2012
 */
public enum TranslationMode {
    /**
     * Base mode.
     */
    BASE("&Default translation"),
    /**
     * Mode for the Software Verification Competition.
     */
    SV_COMP("&SV-Comp features");

    /**
     * The field for the String representation.
     */
    private final String desc;

    /**
     * Constructor.
     * 
     * @param desc
     *            the String representation.
     */
    private TranslationMode(final String desc) {
        this.desc = desc;
    }

    /**
     * Returns a string describing this mode.
     * 
     * @return description string.
     */
    public String toDescString() {
        return desc;
    }
}
