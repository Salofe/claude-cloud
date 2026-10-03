import { Audio } from "@remotion/media";
import { AbsoluteFill, Sequence, staticFile, useVideoConfig } from "remotion";
import { EndCard } from "./components/EndCard";
import { Fade, Flash, Grade } from "./components/Grade";
import { Shot } from "./components/Shot";
import { Headline, Line, Slam, SystemTag } from "./components/Type";
import { GOLD, RED, VIOLET, bar } from "./theme";

export type TrailerProps = {
  /** 1 = full trailer; 7 = only what comes after the first 15 minutes */
  readonly startBar: number;
};

const URL = "play.clawcade.gg/g/LHgYcmEt";

/**
 * Timeline is written in musical bars (120 BPM, 60 frames per bar) so every cut lands on the beat.
 * Sections before `startBar` are skipped by shifting the whole timeline left.
 */
export const Trailer: React.FC<TrailerProps> = ({ startBar }) => {
  const { fps } = useVideoConfig();
  const o = -(startBar - 1) * 60; // timeline offset
  const post = startBar > 1;
  return (
    <AbsoluteFill style={{ backgroundColor: "black" }}>
      <Audio src={staticFile("music.wav")} trimBefore={-o} />
      <Sequence name="timeline" from={o}>
        {/* ---------- 1-2 cold open ---------- */}
        <Sequence name="Open" from={bar(1)} durationInFrames={120} premountFor={fps}>
          <Shot clip="mine-early" trim={20} zoom={[1.25, 1.1]} dim={0.45} blur={2} />
          <Line text="Todo empieza con una roca…" />
        </Sequence>
        {/* ---------- 3-6 early game: mina, vende, mejora ---------- */}
        <Sequence name="Mining" from={bar(3)} durationInFrames={60} premountFor={fps}>
          <Shot clip="mine-early" trim={80} />
        </Sequence>
        <Sequence name="MINA" from={bar(4)} durationInFrames={60} premountFor={fps}>
          <Shot clip="mine-early" trim={140} zoom={[1.1, 1.2]} />
          <Slam text="MINA" />
        </Sequence>
        <Sequence name="VENDE" from={bar(5)} durationInFrames={60} premountFor={fps}>
          <Shot clip="dock-sell" trim={0} zoom={[1.0, 1.03]} dim={0.45} blur={2} />
          <Slam text="VENDE" color={GOLD} />
        </Sequence>
        <Sequence name="MEJORA" from={bar(6)} durationInFrames={60} premountFor={fps}>
          <Shot clip="dock-sell" trim={58} zoom={[1.0, 1.03]} dim={0.45} blur={2} />
          <Slam text="MEJORA" />
        </Sequence>
        {/* ---------- 7 the turn ---------- */}
        <Sequence name="Turn" from={bar(7)} durationInFrames={60} premountFor={fps}>
          <Shot clip="map-dyson" trim={0} zoom={[1.5, 1.2]} dim={0.55} blur={3} />
          <Line text={post ? "Lo que viene después…" : "…y eso es solo el comienzo."} size={84} stagger={4} />
          {post ? <Fade from={1} to={0} /> : null}
        </Sequence>
        {/* ---------- 8-11 explore the solar system ---------- */}
        <Sequence name="Travel" from={bar(8)} durationInFrames={120} premountFor={fps}>
          <Shot clip="map-travel" trim={0} zoom={[1.08, 1.18]} />
          <Headline kicker="Mapa estelar" text="EXPLORA EL SISTEMA SOLAR" />
        </Sequence>
        <Sequence name="Mercury" from={bar(10)} durationInFrames={60} premountFor={fps}>
          <Shot clip="mine-rich" trim={30} />
          <Headline kicker="Platino · Piedra solar" text="MINERALES RAROS" color={GOLD} />
        </Sequence>
        <Sequence name="Saturn" from={bar(11)} durationInFrames={60} premountFor={fps}>
          <Shot clip="mine-saturn" trim={30} />
        </Sequence>
        {/* ---------- 12-13 build an empire ---------- */}
        <Sequence name="Empire" from={bar(12)} durationInFrames={30} premountFor={fps}>
          <Shot clip="empire" trim={10} zoom={[1.0, 1.03]} />
        </Sequence>
        <Sequence name="Projects" from={bar(12, 2)} durationInFrames={30} premountFor={fps}>
          <Shot clip="projects" trim={10} zoom={[1.0, 1.03]} />
        </Sequence>
        <Sequence name="Dyson" from={bar(13)} durationInFrames={60} premountFor={fps}>
          <Shot clip="map-dyson" trim={20} zoom={[1.0, 1.1]} />
        </Sequence>
        <Sequence name="EmpireTitle" from={bar(12)} durationInFrames={120} premountFor={fps}>
          <Headline kicker="Puestos · Cargueros · Megaproyectos" text="CONSTRUYE UN IMPERIO" color={VIOLET} />
        </Sequence>
        {/* ---------- 14-17 defend it ---------- */}
        <Sequence name="Pirates" from={bar(14)} durationInFrames={120} premountFor={fps}>
          <Shot clip="pirates" trim={0} zoom={[1.06, 1.16]} />
          <Headline kicker="Piratas · Guerras · Alianzas" text="DEFIÉNDELO" color={RED} />
        </Sequence>
        <Sequence name="BossSol" from={bar(16)} durationInFrames={120} premountFor={fps}>
          <Shot clip="boss-sol" trim={0} zoom={[1.05, 1.18]} />
          <Headline kicker="Nube de Oort" text="EL GUARDIÁN FINAL" color={RED} />
        </Sequence>
        {/* ---------- 18-19 the jump ---------- */}
        <Sequence name="Jump" from={bar(18)} durationInFrames={120} premountFor={fps}>
          <Shot clip="jump" trim={0} zoom={[1.0, 1.25]} />
          <Sequence from={4} durationInFrames={44}>
            <Line text="Y cuando el Sol sea tuyo…" size={80} stagger={3} />
          </Sequence>
        </Sequence>
        {/* ---------- 20-21 galaxy reveal ---------- */}
        <Sequence name="Galaxy" from={bar(20)} durationInFrames={120} premountFor={fps}>
          <Shot clip="galaxy" trim={0} zoom={[1.2, 1.0]} />
          <Slam text="15 SISTEMAS" size={150} />
        </Sequence>
        {/* ---------- 22-31 systems montage, cut on the beat ---------- */}
        <Sequence name="Centauri" from={bar(22)} durationInFrames={30} premountFor={fps}>
          <Shot clip="map-centauri" trim={20} zoom={[1.2, 1.4]} />
          <SystemTag n={2} name="ALFA CENTAURI" />
        </Sequence>
        <Sequence name="Barnard" from={bar(22, 2)} durationInFrames={30} premountFor={fps}>
          <Shot clip="map-barnard" trim={20} zoom={[1.2, 1.4]} />
          <SystemTag n={3} name="ESTRELLA DE BARNARD" />
        </Sequence>
        <Sequence name="Sirius" from={bar(23)} durationInFrames={60} premountFor={fps}>
          <Shot clip="boss-sirius" trim={50} />
          <SystemTag n={4} name="SIRIO" sub="La Serpiente" color={RED} />
        </Sequence>
        <Sequence name="TauCeti" from={bar(24)} durationInFrames={30} premountFor={fps}>
          <Shot clip="map-tauceti" trim={20} zoom={[1.2, 1.4]} />
          <SystemTag n={5} name="TAU CETI" />
        </Sequence>
        <Sequence name="Eridani" from={bar(24, 2)} durationInFrames={30} premountFor={fps}>
          <Shot clip="map-eridani" trim={20} zoom={[1.2, 1.4]} />
          <SystemTag n={6} name="ÉPSILON ERIDANI" />
        </Sequence>
        <Sequence name="Vega" from={bar(25)} durationInFrames={60} premountFor={fps}>
          <Shot clip="boss-vega" trim={110} />
          <SystemTag n={7} name="VEGA" sub="El Leviatán" color={RED} />
        </Sequence>
        <Sequence name="Altair" from={bar(26)} durationInFrames={30} premountFor={fps}>
          <Shot clip="map-altair" trim={20} zoom={[1.2, 1.4]} />
          <SystemTag n={8} name="ALTAIR" />
        </Sequence>
        <Sequence name="Kepler" from={bar(26, 2)} durationInFrames={30} premountFor={fps}>
          <Shot clip="mine-kepler" trim={20} />
          <SystemTag n={9} name="KEPLER" sub="Rocas vivas" />
        </Sequence>
        <Sequence name="Rigel" from={bar(27)} durationInFrames={60} premountFor={fps}>
          <Shot clip="boss-rigel" trim={20} />
          <SystemTag n={10} name="RIGEL" sub="El Radiante" color={RED} />
        </Sequence>
        <Sequence name="Betelgeuse" from={bar(28)} durationInFrames={60} premountFor={fps}>
          <Shot clip="boss-betelgeuse" trim={0} />
          <SystemTag n={11} name="BETELGEUSE" sub="El Fénix" color={RED} />
        </Sequence>
        <Sequence name="Orion" from={bar(29)} durationInFrames={30} premountFor={fps}>
          <Shot clip="mine-orion" trim={20} />
          <SystemTag n={12} name="NEBULOSA DE ORIÓN" />
        </Sequence>
        <Sequence name="Pulsar" from={bar(29, 2)} durationInFrames={30} premountFor={fps}>
          <Shot clip="mine-pulsar" trim={20} />
          <SystemTag n={13} name="EL PÚLSAR" />
        </Sequence>
        <Sequence name="Rim" from={bar(30)} durationInFrames={60} premountFor={fps}>
          <Shot clip="boss-rim" trim={0} />
          <SystemTag n={14} name="BORDE DEL NÚCLEO" sub="El Arconte" color={RED} />
        </Sequence>
        <Sequence name="SgrMap" from={bar(31)} durationInFrames={60} premountFor={fps}>
          <Shot clip="map-sgra" trim={10} zoom={[1.0, 1.3]} />
          <SystemTag n={15} name="SAGITARIO A*" color={VIOLET} />
        </Sequence>
        {/* ---------- 32-35 finale ---------- */}
        <Sequence name="Devourer" from={bar(32)} durationInFrames={240} premountFor={fps}>
          <Shot clip="boss-sgra" trim={0} zoom={[1.05, 1.25]} />
          <Sequence from={30} durationInFrames={180}>
            <Line text="¿Llegarás al centro de la galaxia?" size={76} />
          </Sequence>
        </Sequence>
        {/* ---------- 36-40 title card ---------- */}
        <Sequence name="EndCard" from={bar(36)} durationInFrames={300} premountFor={fps}>
          <Shot clip="title-bg" trim={0} zoom={[1.15, 1.0]} dim={0.2} />
          <EndCard url={URL} tagline="Mina · Mejora · Conquista la galaxia" cta="Juega gratis en tu navegador" platforms="PC y móvil · Sin descargas · Español" />
        </Sequence>
        {/* flashes on the big hits */}
        {[bar(8), bar(20), bar(22), bar(32), bar(36)].map((f) => (
          <Sequence key={f} from={f} durationInFrames={10}>
            <Flash />
          </Sequence>
        ))}
        {[bar(4), bar(5), bar(6), bar(14), bar(16), bar(23), bar(25), bar(27), bar(28), bar(30)].map((f) => (
          <Sequence key={f} from={f} durationInFrames={6}>
            <Flash len={5} />
          </Sequence>
        ))}
      </Sequence>
      <Grade />
    </AbsoluteFill>
  );
};
