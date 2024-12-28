/**
 *
 * @author Aurora
 */
public class WordleController {
   
    private WordleModel model;
    private WordleView view;

    /**
     * Creates a new instance of WordleController.
     *
     * @param model the WordleModel instance to be associated with the controller
     */
    public WordleController(WordleModel model){
        this.model = model;
    }
    /**
     * Sets the WordleView instance to be associated with the controller.
     *
     * @param view the WordleView instance
     */
    public void setView(WordleView view){
        this.view = view;
    }

    /**
     * Adds the specified button text to the current guess in the model.
     * The addition is only performed if the guess is not complete, the player
     * has not won, and the player still has tries left.
     *
     * @param buttonText the text of the button to be added to the guess
     */
    public void addToGuess(String buttonText){
        if (!model.isGuessComplete() && !model.hasPlayerWon() && model.playerHasTriesLeft())
            model.addToGuess(buttonText);
    }
    public void removeFromGuess(){
        if (model.getGuessWord().length() > 0 && !model.hasPlayerWon() && model.playerHasTriesLeft())
            model.removeFromGuess();
    }
    public void submitGuess(){
        if (model.isGuessComplete() && !model.hasPlayerWon() && model.playerHasTriesLeft()){
            model.submitGuess();
        }
    }
    public void restartGame(){
        model.initGame();
    }
}
