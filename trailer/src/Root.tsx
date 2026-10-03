import { Composition } from "remotion";
import { Trailer } from "./Trailer";
import { Vertical } from "./Vertical";

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition id="Trailer" component={Trailer} durationInFrames={2400} fps={30} width={1920} height={1080} defaultProps={{ startBar: 1 }} />
      <Composition id="TrailerDespues15" component={Trailer} durationInFrames={2040} fps={30} width={1920} height={1080} defaultProps={{ startBar: 7 }} />
      <Composition id="TikTok30" component={Vertical} durationInFrames={900} fps={30} width={1080} height={1920} />
    </>
  );
};
