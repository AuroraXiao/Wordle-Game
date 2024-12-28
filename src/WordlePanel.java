import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import javax.swing.JPanel;

/**
 * The abstract class representing a game panel.
 * It extends JPanel and provides basic functionality for game panels.
 * Subclasses of this class should implement the updateState method.
 *
 * @author Aurora
 */
public abstract class WordlePanel extends JPanel {

    // The size of the panel
    //@ public invariant panelSize != null;
    protected Dimension panelSize;

    // The model associated with the game panel
    //@ public invariant wordleModel != null;
    protected WordleModel wordleModel;

    // The controller associated with the game panel
    //@ public invariant wordleController != null;
    protected WordleController wordleController;
    public final Color GREEN = new Color(106, 170, 100);
    public final Color YELLOW = new Color(201, 180, 88);

    /**
     * Constructs a WordlePanel with the specified model and controller.
     *
     * @param wordleModel the WordleModel associated with the game panel
     * @param wordleController the WordleController associated with the game panel
     */
    //@ requires wordleModel != null;
    //@ requires wordleController != null;
    //@ ensures this.wordleModel == model;
    //@ ensures this.wordleController == controller;
    public WordlePanel(WordleModel wordleModel, WordleController wordleController){

        panelSize = super.getPreferredSize();
        this.wordleModel = wordleModel;
        this.wordleController = wordleController;
    }

    /**
     * Updates the state of the game panel.
     * This method should be implemented by subclasses.
     */
    //@ public abstract normal_behavior
    //@ ensures \old(wordleModel) == model;
    //@ ensures \old(wordleController) == controller;
    public abstract void updateState();

    /**
     * Returns the minimum size of the game panel.
     *
     * @return the minimum size of the panel
     */
    //@ ensures \result != null;
    //@ ensures \result.equals(getPreferredSize());
    @Override
    public Dimension getMinimumSize(){
        return getPreferredSize();
    }

    /**
     * Returns the maximum size of the game panel.
     *
     * @return the maximum size of the panel
     */
    //@ ensures \result != null;
    //@ ensures \result.equals(getPreferredSize());
    @Override
    public Dimension getMaximumSize(){
        return getPreferredSize();
    }

    /**
     * Returns the preferred size of the game panel.
     *
     * @return the preferred size of the panel
     */
    //@ ensures \result != null;
    //@ ensures \result.equals(panelSize);
    @Override
    public Dimension getPreferredSize(){
        return  panelSize;
    }

    /**
     * Returns the alignment on the x-axis for the game panel.
     *
     * @return the alignment on the x-axis
     */
    //@ ensures \result == Component.CENTER_ALIGNMENT;
    @Override
    public float getAlignmentX() {
        return Component.CENTER_ALIGNMENT;
    }
}
