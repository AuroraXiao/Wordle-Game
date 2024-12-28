import java.awt.Dimension;
import java.awt.event.ActionEvent;
import javax.swing.JButton;
import javax.swing.JLabel;
/**
 *
 * @author Aurora
 */

/**
 * The BasePanel class represents a panel in the Wordle game.
 * It extends the WordlePanel class.
 * It contains components such as a reset button, error label, and answer label.
 */
public class BasePanel extends WordlePanel {
    
    private /*@ spec_public @*/ JButton resetGameButton;
    private /*@ spec_public @*/ JLabel errorLabel;
    private /*@ spec_public @*/ JLabel answerLabel;

    /**
     * Constructs a BasePanel object with the specified model and controller.
     *
     * @param model      the WordleModel object
     * @param controller the WordleController object
     */
    //@ requires model != null;
    //@ requires controller != null;
    //@ ensures super.panelSize.equals(new Dimension(420, 45));
    //@ ensures resetGameButton != null;
    //@ ensures errorLabel != null;
    //@ ensures answerLabel != null;
    //@ ensures resetGameButton.isEnabled() == false;
    //@ ensures errorLabel.isVisible() == false;
    //@ ensures answerLabel.isVisible() == false;
    public BasePanel(WordleModel model, WordleController controller){
        super(model, controller);
        super.panelSize = new Dimension(420,45);
        createBasePanel();
    }

    /**
     * Creates the base panel by initializing the components and adding them to the panel.
     */
    //@ ensures resetGameButton != null;
    //@ ensures errorLabel != null;
    //@ ensures answerLabel != null;
    //@ ensures resetGameButton.isEnabled() == false;
    //@ ensures errorLabel.isVisible() == false;
    //@ ensures answerLabel.isVisible() == false;
    private void createBasePanel(){
        
        resetGameButton = new JButton("Restart");
        errorLabel = new JLabel("Word Not in List!");
        answerLabel = new JLabel("Answer: " + wordleModel.getAnswer());
        resetGameButton.setEnabled(false);
        errorLabel.setVisible(false);
        answerLabel.setVisible(false);
        
        resetGameButton.addActionListener((ActionEvent e) -> {
            wordleController.restartGame();});
        
        this.add(resetGameButton);
        this.add(answerLabel);
        this.add(errorLabel);
    }

    /**
     * Updates the state of the panel based on the current state of the model.
     */
    //@ ensures resetGameButton.isEnabled() == model.allowNewGame();
    //@ ensures !resetGameButton.isEnabled() ==> answerLabel.getText().equals("Answer: " + model.getAnswer());
    //@ ensures errorLabel.isVisible() == model.isWordNotInList();
    //@ ensures answerLabel.isVisible() == (model.isShowAnswer() || model.alwaysShowAnswer());
    @Override
    public void updateState(){
        if(wordleModel.allowNewGame())
            resetGameButton.setEnabled(true);
        if(wordleModel.hasNewGameStarted()){
            resetGameButton.setEnabled(false);
            answerLabel.setText("Answer: " + wordleModel.getAnswer());
        }
        if(wordleModel.isWordNotInList())
            errorLabel.setVisible(true);
        else
            errorLabel.setVisible(false);
  
        if(wordleModel.isShowAnswer() || wordleModel.alwaysShowAnswer())
            answerLabel.setVisible(true);
        else
            answerLabel.setVisible(false);
    }
}
