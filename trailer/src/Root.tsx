import { Composition } from "remotion";
import { Trailer } from "./Trailer";

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition id="Trailer" component={Trailer} durationInFrames={2400} fps={30} width={1920} height={1080} defaultProps={{ startBar: 1 }} />
      <Composition id="TrailerDespues15" component={Trailer} durationInFrames={2040} fps={30} width={1920} height={1080} defaultProps={{ startBar: 7 }} />
    </>
  );
};
